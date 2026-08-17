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
\echo '=== Q8. May I quote it? (authority, not support)'
\echo '    ProvSQL ships a user-defined capability semiring in its own test'
\echo '    suite (test/sql/capability.sql): bitwise OR / AND over a permission'
\echo '    lattice. So the second dimension is not outside the tool.'

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
-- Measured 2026-08-17, PostgreSQL 16.10 / ProvSQL 1.13.0-dev, this machine.
--
-- Q1,Q2,Q3  both. Plain arithmetic; provenance is not what answers them.
--
-- Q4  NO, and the reason is structural rather than a missing feature. Every
--     base row is its own variable, so `quoted` — a figure standing on
--     nothing — gets a formula too: the bare token `92b6b585…`. A fact
--     supported by a document and a fact supported by itself are the same
--     kind of object here. Detecting the second degenerates to `ground IS
--     NULL`, which plain SQL already does; provenance adds nothing.
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
-- Q8  Not in stock, but its own test suite defines a capability semiring
--     over a permission lattice, so authority-as-a-second-dimension is a
--     product semiring away, not a limitation.
--
-- THE BRACKET, both halves.
--     `support(sum(amount))` = **[0, 6500]** — a real interval over
--     magnitudes, and it is the UNCONDITIONAL range across all worlds: it
--     stayed [0, 6500] after conditioning, because support() ignores the
--     probabilities. So ProvSQL brackets a total, and does not narrow the
--     bracket to a scenario.
--     The epistemic half is different and is where the ledger still stands.
--     `inv17 ⊕ invoice17` at p=0.9 each evaluates to **0.9900**, with
--     probability_bounds **[0.99, 0.99]** — a point of zero width. If the
--     two names are one piece of paper the true figure is 0.9, and nothing
--     in the output says the difference was assumed away. Not a defect:
--     independence is the model's premise. It is the one place where
--     reporting the assumption as a bracket is a different instrument.
--
-- UNITS.  `sum(amount)` over 2000 EUR and 40 hours returns **2040**,
--     silently. The refusal survives — and it is a type-system property, not
--     a provenance one; a Postgres domain or composite type would do it
--     without ProvSQL's involvement. Worth little.
--
-- THE OBJECTION, and it holds. Reading A returns **0.9900**, reading B
--     returns **0.9000**. So [0.90, 0.99] — the ledger's bracket — is
--     COMPUTABLE IN PROVSQL, by encoding the ledger twice and taking both
--     ends. What the ledger has is not a capability the older tool lacks. It
--     is a DEFAULT: it computes both readings unasked and refuses to print a
--     bare number, where ProvSQL prints 0.9900 unless you knew to ask twice.
--     Stated plainly because it is the last thing the note claimed as its
--     own, and it did not survive being run.
--
-- NET.  Of the four properties the note claimed, none is a capability gap.
-- Magnitudes: gone, ProvSQL has them. Authority and the earned/credit grade:
-- user-defined semirings — a two-element lattice with min as multiplication,
-- and a product of two — which ProvSQL supports and nobody has written.
-- Units: real, and not a provenance question at all. The bracket: a default,
-- shown above.
--
-- WHAT IS LEFT IS NOT THE LEDGER. It is this file. Eight auditor questions
-- asked of a working provenance system, with two answers an auditor should
-- not accept: a figure standing on nothing carries a token exactly like a
-- documented one, and an unverifiable independence is reported as 0.9900
-- with bounds of zero width. Both are correct behaviour under the model's
-- premises. Neither is the answer to the question that was asked.
