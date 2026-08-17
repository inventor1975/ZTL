-- The eight auditor questions, asked of REAL ProvSQL.
--
-- `db/probe_provenance.py` compared the FORMALISM because Postgres was not on
-- the machine. It now is: PostgreSQL 16 with ProvSQL 1.13.0-dev built from
-- source. This file asks the same eight questions of the shipped tool, so the
-- comparison stops being an argument about what a semiring could do and
-- becomes a record of what the package does.
--
-- The expectation was written down BEFORE the run, in the session log: 5, 6
-- and 7 close cleanly (lineage is ProvSQL's subject); units, the earned/credit
-- grade and the bracket do not. The results below are what actually happened.
--
-- Run:  psql -d provtest -v ON_ERROR_STOP=1 -f db/provsql_ledger.sql
-- Setup: CREATE EXTENSION provsql CASCADE; SELECT provsql.setup_search_path();
--        (shared_preload_libraries = 'provsql' in postgresql.conf)

\pset format aligned
\set ON_ERROR_STOP on

-- FIRST LINE OF OUTPUT IS THE ENVIRONMENT, and it is not decoration. The note
-- built on this file quoted "PostgreSQL 16.10"; this machine runs 16.14 and
-- never ran 16.10, and the error survived the repo's own figure scan because
-- a version string sat on that scan's exemption list. So the live version is
-- printed on every run: a machine that has moved on contradicts the record
-- instead of silently outdating it.
SELECT version() AS server,
       extversion AS provsql FROM pg_extension WHERE extname = 'provsql';

DROP TABLE IF EXISTS ledger CASCADE;
DROP TABLE IF EXISTS names;

-- The same day-one ledger as probe_provenance.py, plus one row in another
-- unit, because "refuses to add incommensurable magnitudes" is one of the
-- four properties still claimed.
CREATE TABLE ledger(name text, amount numeric, unit text, ground text,
                    grade text);
INSERT INTO ledger VALUES
  ('line_a',  3000, 'EUR',   'inv17',     'earned'),
  ('line_b',  1500, 'EUR',   'inv17',     'earned'),
  ('line_c',  2000, 'EUR',   'inv18',     'earned'),
  ('quoted',  1200, 'EUR',   NULL,        'credit'),
  ('ceiling', 9000, 'EUR',   'contract',  'earned'),
  ('paid',    5000, 'EUR',   NULL,        'credit'),
  ('effort',    40, 'hours', 'timesheet', 'earned');

SELECT add_provenance('ledger');
SELECT create_provenance_mapping('names', 'ledger', 'ground');

\echo ''
\echo '=== Q4. Which figures have never been documented?'
\echo '    (what does the provenance formula show for an ungrounded row?)'
SELECT name, grade, sr_formula(provsql, 'names') AS formula
  FROM ledger ORDER BY name;

\echo ''
\echo '=== Q5. What rests on inv-17?'
SELECT name FROM ledger WHERE sr_formula(provsql, 'names') = 'inv17';

\echo ''
\echo '=== Q1/Q2/Q3. The plain figures, and the aggregate row provenance'
CREATE TABLE q123 AS
  SELECT sum(amount) AS billed, sr_formula(provenance(), 'names') AS rowprov
    FROM ledger WHERE name LIKE 'line%';
SELECT remove_provenance('q123');
SELECT * FROM q123;
DROP TABLE q123;

\echo ''
\echo '=== Q7a. The bracket: support(sum) — the interval the total can take'
\echo '    across possible worlds (every row present or absent).'
DO $$ BEGIN PERFORM set_prob(provenance(), 0.5) FROM ledger; END $$;
CREATE TABLE q7a AS
  SELECT (support(sum(amount))).lo AS lo, (support(sum(amount))).hi AS hi
    FROM ledger WHERE name LIKE 'line%';
SELECT remove_provenance('q7a');
SELECT * FROM q7a;
DROP TABLE q7a;

\echo ''
\echo '=== Q6/Q7b. inv-17 is forged. What falls, and what do the numbers'
\echo '    become? Withdrawal = probability 0; the surviving world = 1.'
DO $$ BEGIN
  PERFORM set_prob(provenance(), CASE WHEN ground = 'inv17' THEN 0 ELSE 1 END)
    FROM ledger WHERE ground IS NOT NULL;
  PERFORM set_prob(provenance(), 1) FROM ledger WHERE ground IS NULL;
END $$;
CREATE TABLE q7b AS
  SELECT expected(sum(amount)) AS billed_after,
         (support(sum(amount))).lo AS lo, (support(sum(amount))).hi AS hi
    FROM ledger WHERE name LIKE 'line%';
SELECT remove_provenance('q7b');
SELECT * FROM q7b;
DROP TABLE q7b;

\echo ''
\echo '=== The unit question: does sum() refuse to add EUR to hours?'
CREATE TABLE qunit AS
  SELECT sum(amount) AS mixed_total FROM ledger
   WHERE name IN ('line_c', 'effort');
SELECT remove_provenance('qunit');
SELECT * FROM qunit;
DROP TABLE qunit;

\echo ''
\echo '=== Q4 AND Q8, REOPENED BY REVIEW — both answered by SHIPPED semirings.'
\echo '    An earlier version of this file said the earned/credit grade was a'
\echo '    semiring "nobody has written". sr_maxmin is a compiled built-in:'
\echo '    (+) = enum-max, (*) = enum-min over any ENUM. One CREATE TYPE.'
DROP TABLE IF EXISTS zg CASCADE;
DROP TABLE IF EXISTS zgmap;
DROP TABLE IF EXISTS zgb;
DROP TYPE IF EXISTS zgrade CASCADE;
CREATE TYPE zgrade AS ENUM ('credit', 'earned');
CREATE TABLE zg(name text, amount numeric, ground text, grade zgrade);
INSERT INTO zg VALUES ('line_a', 3000, 'inv17', 'earned'),
                      ('line_c', 2000, 'inv18', 'earned'),
                      ('quoted', 1200, NULL,    'credit');
SELECT add_provenance('zg');
SELECT create_provenance_mapping('zgmap', 'zg', 'grade');
CREATE TABLE zgb AS
  SELECT a.name || ' x ' || b.name AS pair,
         sr_maxmin(provenance(), 'zgmap', 'credit'::zgrade) AS grade
    FROM zg a, zg b WHERE a.name < b.name;
SELECT remove_provenance('zgb');
SELECT pair, grade FROM zgb ORDER BY pair;
DROP TABLE zgb; DROP TABLE zgmap;
SELECT remove_provenance('zg'); DROP TABLE zg; DROP TYPE zgrade;
\echo '    And Q8 the same way: sr_minmax is the shipped dual, demonstrated in'
\echo '    ProvSQL''s own documentation under "Minimum Security Clearance".'

\echo ''
\echo '=== The independence question, measured on the engine'
DROP TABLE IF EXISTS twonames CASCADE;
DROP TABLE IF EXISTS tn_map;
DROP TABLE IF EXISTS tn CASCADE;
CREATE TABLE twonames(doc text, amount numeric);
INSERT INTO twonames VALUES ('inv17', 3000), ('invoice17', 3000);
SELECT add_provenance('twonames');
SELECT create_provenance_mapping('tn_map', 'twonames', 'doc');
DO $$ BEGIN PERFORM set_prob(provenance(), 0.9) FROM twonames; END $$;
-- DISTINCT on the one column merges the two rows, so the semiring ADDS:
-- the output stands if either document does.
CREATE TABLE tn AS SELECT DISTINCT amount FROM twonames WHERE amount = 3000;
SELECT sr_formula(provsql, 'tn_map') AS f,
       round(probability_evaluate(provsql)::numeric, 4) AS p,
       (probability_bounds(provsql)).*
  FROM tn;
DROP TABLE tn;
DROP TABLE tn_map;
SELECT remove_provenance('twonames');
DROP TABLE twonames;

\echo ''
\echo '=== AND THE OBJECTION TO OUR OWN CLAIM, run rather than argued.'
\echo '    If the bracket is just the two readings of "are these one paper",'
\echo '    ProvSQL can compute BOTH ENDS ITSELF — encode the ledger twice.'
DROP TABLE IF EXISTS w2 CASCADE;
DROP TABLE IF EXISTS w1 CASCADE;
DROP TABLE IF EXISTS m2;
DROP TABLE IF EXISTS m1;
DROP TABLE IF EXISTS r2;
DROP TABLE IF EXISTS r1;
-- READING A: two names, two papers.
CREATE TABLE w2(doc text, amount numeric);
INSERT INTO w2 VALUES ('inv17', 3000), ('invoice17', 3000);
SELECT add_provenance('w2');
SELECT create_provenance_mapping('m2', 'w2', 'doc');
DO $$ BEGIN PERFORM set_prob(provenance(), 0.9) FROM w2; END $$;
CREATE TABLE r2 AS SELECT DISTINCT amount FROM w2 WHERE amount = 3000;
-- READING B: two names, one paper.
CREATE TABLE w1(doc text, amount numeric);
INSERT INTO w1 VALUES ('inv17', 3000);
SELECT add_provenance('w1');
SELECT create_provenance_mapping('m1', 'w1', 'doc');
DO $$ BEGIN PERFORM set_prob(provenance(), 0.9) FROM w1; END $$;
CREATE TABLE r1 AS SELECT DISTINCT amount FROM w1 WHERE amount = 3000;
SELECT sr_formula(provsql, 'm2') AS reading_a,
       round(probability_evaluate(provsql)::numeric, 4) AS p FROM r2;
SELECT sr_formula(provsql, 'm1') AS reading_b,
       round(probability_evaluate(provsql)::numeric, 4) AS p FROM r1;
DROP TABLE r2; DROP TABLE r1; DROP TABLE m2; DROP TABLE m1;
SELECT remove_provenance('w2');
SELECT remove_provenance('w1');
DROP TABLE w2; DROP TABLE w1;

DROP TABLE names;
SELECT remove_provenance('ledger');
DROP TABLE ledger;

-- ============================================================ WHAT IT SAID
-- Measured 2026-08-17 on this machine; the run prints its own server and
-- extension versions as its first line, which is the record.
--
-- Q1,Q2,Q3  both. Plain arithmetic; provenance is not what answers them.
--
-- Q4  Answered "no" here for a day, and REVIEW REFUTED IT. It is true that
--     the DEFAULT mapping gives `quoted` a bare token like any document. It
--     is false that the distinction has nowhere to live: the leaf annotation
--     is whatever `create_provenance_mapping` is pointed at — a column OR an
--     expression, e.g. `(ground IS NOT NULL)` — and `sr_boolean` then carries
--     it to derived rows, which `WHERE ground IS NULL` cannot do. And the
--     graded form ships: see the sr_maxmin block above.
--
-- Q5  YES, cleanly.  `sr_formula(provsql,'names') = 'inv17'` -> line_a,line_b.
--
-- Q6  YES.  Withdrawal is set_prob(token, 0).
--
-- Q7  YES, AND EXACTLY — this is the result that went against the prediction
--     written down beforehand. `expected(sum(amount))` with inv-17's rows at
--     probability 0 and the rest at 1 returns **2000**: the correct post-
--     withdrawal figure. ProvSQL carries MAGNITUDES through aggregation
--     (expected / variance / moments / support), which `probe_provenance.py`
--     had claimed semirings do not do. That claim was wrong about the
--     shipped tool and has been corrected there.
--
-- Q8  Said "not in stock" here, and that was wrong too. `sr_minmax` is a
--     shipped built-in and ProvSQL's documentation demonstrates it as
--     Minimum Security Clearance: the clearance needed to have inferred a
--     derived fact. That IS question 8.
--
-- THE BRACKET, both halves.
--     `support(sum(amount))` = **[0, 6500]** — a real interval over
--     magnitudes, and it is the UNCONDITIONAL range across all worlds: it
--     stayed [0, 6500] after conditioning, because support() ignores the
--     probabilities. So ProvSQL brackets a total, and does not narrow the
--     bracket to a scenario.
--     The epistemic half: `inv17 ⊕ invoice17` at p=0.9 each evaluates to
--     **0.9900**, with probability_bounds **[0.99, 0.99]** — a point of zero
--     width. If the two names are one piece of paper the true figure is 0.9.
--     Not a defect and NOT a property of the formalism either, which is how
--     an earlier version of this file put it: ProvSQL's manual states it as
--     a default — "correlations between tuples are not modelled. To model
--     correlated probabilities, derive them explicitly with queries" — and
--     ships `repair_key` for the block-independent-disjoint case, with tests.
--
-- UNITS.  `sum(amount)` over 2000 EUR and 40 hours returns **2040**,
--     silently. The refusal survives — and it is a type-system property, not
--     a provenance one; a Postgres domain or composite type would do it
--     without ProvSQL's involvement. Worth little.
--
-- THE OBJECTION, and it holds. Reading A returns **0.9900**, reading B
--     returns **0.9000**. So [0.90, 0.99] — the ledger's bracket — is
--     COMPUTABLE IN PROVSQL. This file first said that took two encodings
--     combined by hand; review showed it takes ONE statement — point the
--     second row's `provsql` column at the first row's token and the same
--     query returns 0.9000. What the ledger has is a DEFAULT, not a
--     capability, and even the concession was too generous to us.
--
-- NET, after review.  NOTHING HERE IS OURS. Magnitudes: shipped. Grade and
-- permission: shipped, `sr_maxmin` and `sr_minmax`, demonstrated above on
-- this file's own ledger for the price of a CREATE TYPE. The bracket: a
-- default, and one UPDATE from the other reading. Units: not a provenance
-- question at all.
--
-- THE SHAPE OF THE ERROR, because it happened three times. Each round
-- withdrew a claim and kept a remainder; each next round found the remainder
-- was also available; and every time the conclusion "the tool does not do X"
-- had been reached by reasoning rather than by reading the function list.
-- `\df provsql.sr_*` would have ended it on day one. What that measures is
-- distance from the frontier, not just an error. The file is kept because
-- the comparison is true and reproducible. Nothing is claimed from it.
