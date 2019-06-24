-- Copyright (c) 2018 Chucky Ellison <cme at freefour.com>, 2019 Kassym Dorsel
-- Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation
-- files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy,
-- modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the
-- Software is furnished to do so, subject to the following conditions:
-- The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
-- THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE
-- WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
-- COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE,
-- ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

-- based on code from John D. Cook's https://www.johndcook.com/blog/skewness_kurtosis/ with permission
-- based on code from the P2 Algorithm for Dynamic Quantiles https://www.cse.wustl.edu/~jain/papers/ftp/psqr.pdf

-- Notes:
-- All the math is done at double precision; can easily be changed to work with numeric or single, or whatever.
-- Kurtosis and skewness are NOT corrected for statistical bias

--------------------------------------------------
-- MAKE SURE you're not using any of these names!

-- drop aggregate if exists stats_agg(double precision);
-- drop function if exists _stats_agg_p2_parabolic(_stats_agg_accum_type, double precision, double precision);
-- drop function if exists _stats_agg_p2_linear(_stats_agg_accum_type, double precision, double precision);
-- drop function if exists _stats_agg_accumulator(_stats_agg_accum_type, double precision);
-- drop function if exists _stats_agg_combiner(_stats_agg_accum_type, _stats_agg_accum_type);
-- drop function if exists _stats_agg_finalizer(_stats_agg_accum_type);
-- drop type if exists _stats_agg_result_type;
-- drop type if exists _stats_agg_accum_type;

CREATE OR REPLACE FUNCTION array_sort(ANYARRAY)
RETURNS ANYARRAY LANGUAGE SQL
AS $$
SELECT ARRAY(SELECT unnest($1) ORDER BY 1)
$$;

create type _stats_agg_accum_type AS (
	cnt bigint,
	min double precision,
	max double precision,
	m1 double precision,
	m2 double precision,
	m3 double precision,
	m4 double precision,

	-- P2 Algorithm
	q double precision[],
	n double precision[],
	np  double precision[],
	dn  double precision[]
);

create type _stats_agg_result_type AS (
	count bigint,
	min double precision,
	max double precision,
	mean double precision,
	stddev double precision,
	skewness double precision,
	kurtosis double precision,

	-- P2 Algorithm
	q25 double precision,
	q50 double precision,
	q75 double precision
);

create or replace function _stats_agg_p2_parabolic(_stats_agg_accum_type, double precision, double precision)
returns double precision AS '
DECLARE
	a alias for $1;
	i alias for $2;
	d alias for $3;
BEGIN
	RETURN a.q[i] + d / (a.n[i + 1] - a.n[i - 1]) * ((a.n[i] - a.n[i - 1] + d) * (a.q[i + 1] - a.q[i]) / (a.n[i + 1] - a.n[i]) + (a.n[i + 1] - a.n[i] - d) * (a.q[i] - a.q[i - 1]) / (a.n[i] - a.n[i - 1]));
END;
'
language plpgsql strict;

create or replace function _stats_agg_p2_linear(_stats_agg_accum_type, double precision, double precision)
returns double precision AS '
DECLARE
	a alias for $1;
	i alias for $2;
	d alias for $3;
BEGIN
	return a.q[i] + d * (a.q[i + d] - a.q[i]) / (a.n[i + d] - a.n[i]);
END;
'
language plpgsql strict;

create or replace function _stats_agg_accumulator(_stats_agg_accum_type, double precision)
returns _stats_agg_accum_type AS '
DECLARE
	a ALIAS FOR $1;
	x alias for $2;
	n1 bigint;
	k bigint;
	d double precision;
	qp double precision;
	delta double precision;
	delta_n double precision;
	delta_n2 double precision;
	term1 double precision;
BEGIN
	n1 = a.cnt;
	a.cnt = a.cnt + 1;
	delta = x - a.m1;
	delta_n = delta / a.cnt;
	delta_n2 = delta_n * delta_n;
	term1 = delta * delta_n * n1;
	a.m1 = a.m1 + delta_n;
	a.m4 = a.m4 + term1 * delta_n2 * (a.cnt*a.cnt - 3*a.cnt + 3) + 6 * delta_n2 * a.m2 - 4 * delta_n * a.m3;
	a.m3 = a.m3 + term1 * delta_n * (a.cnt - 2) - 3 * delta_n * a.m2;
	a.m2 = a.m2 + term1;
	a.min = least(a.min, x);
	a.max = greatest(a.max, x);

	if a.cnt <= 5 then
		a.q = array_append(a.q, x);
		if a.cnt = 5 then
			a.q = array_sort(a.q);
		end if;
		return a;
	end if;

	case
		when x < a.q[1] then
			a.q[1] = x;
			k = 1;
		when x >= a.q[1] and x < a.q[2] then
			k = 1;
		when x >= a.q[2] and x < a.q[3] then
			k = 2;
		when x >= a.q[3] and x < a.q[4] then
			k = 3;
		when x >= a.q[4] and x <= a.q[5] then
			k = 4;
		when x > a.q[5] then
			a.q[5] = x;
			k = 4;
	end case;

	for ii in 1..5 loop
		if ii > k then
			a.n[ii] = a.n[ii] + 1;
		end if;
		a.np[ii] = a.np[ii] + a.dn[ii];
	end loop;

	for ii in 2..4 loop
		d = a.np[ii] - a.n[ii];
		if (d >= 1 and a.n[ii+1] - a.n[ii] > 1) or (d <= -1 and a.n[ii-1] - a.n[ii] < -1) then
			d = sign(d);
			qp = _stats_agg_p2_parabolic(a, ii, d);
			if qp > a.q[ii-1] and qp < a.q[ii+1] then
				a.q[ii] = qp;
			else
				a.q[ii] = _stats_agg_p2_linear(a, ii, d);
			end if;
			a.n[ii] = a.n[ii] + d;
		end if;
	end loop;

	return a;
END;
'
language plpgsql strict;

create or replace function _stats_agg_combiner(_stats_agg_accum_type, _stats_agg_accum_type)
returns _stats_agg_accum_type AS '
DECLARE
	a alias for $1;
	b alias for $2;
	c _stats_agg_accum_type;
	delta1 double precision;
	delta2 double precision;
	delta3 double precision;
	delta4 double precision;
	addA boolean;
	addB boolean;
BEGIN
	addA = a.cnt <= 5;
	addB = b.cnt <= 5;
	if addA and not addB then
		c = b;
	elsif addB and not addA then
		c = a;
	else
		c.cnt = a.cnt + b.cnt;
		for ii in 2..4 loop
			c.q[ii] = (a.q[ii] + b.q[ii]) / 2;
		end loop;
	end if;
	for ii in 1..5 loop
		if addA and ii <= a.cnt then
			c = _stats_agg_accumulator(c, a.q[ii]);
		end if;
		if addB and ii <= b.cnt then
			c = _stats_agg_accumulator(c, b.q[ii]);
		end if;
	end loop;

	delta1 = b.m1 - a.m1;
	delta2 = delta1 * delta1;
	delta3 = delta1 * delta2;
	delta4 = delta2 * delta2;

	c.min = least(a.min, b.min);
	c.max = greatest(a.max, b.max);

	c.m1 = (a.cnt*a.m1 + b.cnt*b.m1) / c.cnt;
	c.m2 = a.m2 + b.m2 + delta2 * a.cnt * b.cnt / c.cnt;
	c.m3 = a.m3 + b.m3 + delta3 * a.cnt * b.cnt * (a.cnt - b.cnt)/(c.cnt*c.cnt);
	c.m3 = c.m3 + 3.0*delta1 * (a.cnt*b.m2 - b.cnt*a.m2) / c.cnt;
	c.m4 = a.m4 + b.m4 + delta4*a.cnt*b.cnt * (a.cnt*a.cnt - a.cnt*b.cnt + b.cnt*b.cnt) / (c.cnt*c.cnt*c.cnt);
	c.m4 = c.m4 + 6.0*delta2 * (a.cnt*a.cnt*b.m2 + b.cnt*b.cnt*a.m2)/(c.cnt*c.cnt) + 4.0*delta1*(a.cnt*b.m3 - b.cnt*a.m3) / c.cnt;

	RETURN c;
END;
'
language plpgsql strict;

create or replace function _stats_agg_finalizer(_stats_agg_accum_type)
returns _stats_agg_result_type AS '
BEGIN
	RETURN row(
		$1.cnt,
		$1.min,
		$1.max,
		$1.m1,
		case when $1.cnt = 1 then null else sqrt($1.m2 / ($1.cnt - 1.0)) end,
		case when $1.m2 = 0 then null else sqrt($1.cnt) * $1.m3 / ($1.m2 ^ 1.5) end,
		case when $1.m2 = 0 then null else $1.cnt * $1.m4 / ($1.m2 * $1.m2) - 3.0 end,
		$1.q[2],
		$1.q[3],
		$1.q[4]
	);
END;
'
language plpgsql strict;

create aggregate stats_agg(double precision) (
	sfunc = _stats_agg_accumulator,
	stype = _stats_agg_accum_type,
	finalfunc = _stats_agg_finalizer,
	combinefunc = _stats_agg_combiner,
	parallel = safe,
	initcond = '(0,,, 0, 0, 0, 0, {}, "{1,2,3,4,5}", "{1,2,3,4,5}", "{0,0.25,0.5,0.75,1}")'
);
