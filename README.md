# JonnyLean

**English** | [日本語](docs/README.ja.md)

A Lean 4 library for formal mathematics and verified programs, with a workflow that connects written specifications, checked proofs, and independent AI reviews. Humans choose the mathematical goals; AI agents implement and review the proofs; Lean checks the formal statements.

The library starts with elementary number theory and combinatorics and extends to polynomial algebra, finite linear algebra, regular expressions, parsers, compilers, and program logic.

## At a glance

| v4 library | Count |
| --- | ---: |
| Tasks, each with a specification and independent contract | 300 |
| Mathematics modules | 178 |
| Explicitly declared named theorems | 1,121 |
| Automated tests passed in local validation | 93 |

The latest recorded local validation passed all 300 tasks and their independent AI review checks. A clean build from the generated source archive also passed all 300 tasks. The full audit covers 179 modules including the aggregate entry point and 3,938 declarations, including 2,555 theorem entries generated or retained by Lean. These audit counts differ from the explicit source theorem count above. See the [validation record (Japanese)](docs/validation.md).

## Quick start

Requirements: **Python 3.11+** and **[elan / Lake](https://github.com/leanprover/elan)**. The project pins **Lean 4.29.1** and uses only the libraries bundled with Lean. Mathlib and additional Python packages are not required.

```sh
git clone https://github.com/nktkt/JonnyLean.git
cd JonnyLean

# Rebuild, audit the library, check every contract, and validate saved AI reviews.
python3 tools/jonnylean.py run all --jobs 4

# Run the automated tests.
python3 -m unittest discover -s tests -v
```

The first invocation may download the pinned Lean toolchain through elan. Rechecking the library does **not** call an AI service or require an AI account.

Open the generated `artifacts/index.html` to browse tasks, theorem types, axiom dependencies, and review status. It is an offline HTML report with search and filters. Each task also gets `artifacts/JL-NNN/report.json` and `report.md`.

## A proof you can use

The regular-expression matcher computes derivatives of a regular expression. Its correctness theorem connects the executable Boolean result to the separately defined language semantics:

```lean
import JonnyLean.RegularExpressions.Matcher
open JonnyLean.RegularExpressions

#eval accepts (.star (.atom 'a')) ['a', 'a'] -- true
#eval accepts (.star (.atom 'a')) ['a', 'b'] -- false

example {α : Type} [DecidableEq α] (r : Regex α) (w : List α) :
    accepts r w = true ↔ denotes r w :=
  accepts_correct r w
```

Import a specific module to use one part of the library, or `import JonnyLean` for the full library. The [mathematics guide (Japanese)](docs/mathematics.md) includes matrix and imperative-program examples.

## Library coverage

| Tasks | Topics |
| --- | --- |
| JL-001–025 | Parity, divisibility, congruence, finite sums, factorials, Fibonacci numbers, affine iteration |
| JL-026–045 | Predicates, maps, relations, finite sets, sorting, state traversal, deduplication, search |
| JL-046–060 | Graphs, walks, reachability, word enumeration, binomial counting, discrete distributions |
| JL-061–080 | GCD and LCM, Euclid's algorithm, reduced pairs, modular computation, finite products |
| JL-081–100 | Coefficient-list polynomials, multiplication, composition, formal derivatives, product and chain rules |
| JL-101–120 | Binary trees, traversals, folds, persistent stacks, queues, association maps |
| JL-121–140 | Expression transformations, stack machines, compiler correctness, stack-depth checking, decompilation |
| JL-141–160 | Constructive language algebra, Kleene closure, automata, state maps, invariants, finite carriers |
| JL-161–180 | Products, subsequences, permutations, shuffles, finite measures, expectation numerators, kernels |
| JL-181–220 | Natural-number vectors and matrices, multiplication, transpose, trace, blocks, powers, outer products |
| JL-221–260 | Regex derivatives and matching, parser combinators, prefix parsing, encoding and decoding round trips |
| JL-261–300 | Imperative semantics, fuel-bounded execution, Hoare logic, verified loops, semantics-preserving optimization |

The [task index (Japanese)](roadmaps/elementary.md) links every specification, Lean implementation, and contract. Specifications and detailed guides currently use Japanese; Lean declarations and CLI commands use English names.

Scope is explicit: matrices and polynomial coefficients use natural numbers; polynomial differentiation is formal; finite probability uses natural-number weights and expectation numerators. Hoare triples express partial correctness, with termination proved separately for selected example programs. General real analysis and measure theory are outside the current library.

## Explore and verify

```sh
python3 tools/jonnylean.py catalog list
python3 tools/jonnylean.py catalog search fibonacci
python3 tools/jonnylean.py catalog show JL-042
python3 tools/jonnylean.py catalog stats
python3 tools/jonnylean.py plan JL-300 --include-dependencies
python3 tools/jonnylean.py library search "derivative evaluate" --kind theorem
python3 tools/jonnylean.py library show JonnyLean.RegularExpressions.accepts_correct

# Mechanical verification only, or verification plus saved review checks.
python3 tools/jonnylean.py verify all --jobs 4
python3 tools/jonnylean.py run all --domain graph-theory --jobs 4
python3 tools/jonnylean.py run all --changed HEAD

# Deterministic partitioning for separate CI checkouts.
python3 tools/jonnylean.py plan all --shard 1/4 --format json
python3 tools/jonnylean.py run all --shard 1/4 --jobs 2
```

`plan` is read-only. `library` searches actual declaration types from a current completed audit and rejects stale evidence. Task selection limits the contracts checked; mechanical auditing still covers the whole mathematics library. Parallel verification shares a fresh whole-library audit within that invocation and checks for input changes throughout the batch.

## What verification means

Each task has a written specification, a named Lean theorem, an independently stated contract, and an AI review against seven criteria. Contracts check the expected proposition rather than inferring it from the implementation. The verifier checks all source modules and contracts with warnings treated as errors, compares source and compiled imports, and audits axiom dependencies, including private and unused declarations.

Only `propext` and `Quot.sound` are allowed axiom dependencies. The project rejects `sorryAx`, custom axioms, and `Classical.choice`.

Mechanical evidence is tied to the whole project's verification inputs. Semantic reviews are tied to a task and its dependency scope. Changes invalidate the corresponding evidence; CI does not approve a review by rewriting its hashes. `run` and `review` validate existing review records without invoking an AI model.

AI reviews are self-reported evidence, not authenticated signatures or formal proofs that prose and Lean are equivalent. Human approval is recorded separately and is currently unrecorded. Verification trusts the Lean toolchain and local execution environment; it does not provide an independent kernel or OS sandbox for hostile Lean code.

## Optional AI worker

The local worker uses an authenticated Codex CLI installation to generate candidates and request a separate AI review. Configure limits in `worker.toml` and check the environment before starting:

```sh
python3 tools/jonnylean.py doctor
python3 tools/jonnylean.py work --task JL-001
python3 tools/jonnylean.py status
python3 tools/jonnylean.py report JOB_ID
python3 tools/jonnylean.py adopt JOB_ID
python3 tools/jonnylean.py resume JOB_ID
```

Each job works on a source snapshot. The author may propose changes only to allowed Lean files; specifications, contracts, verification tools, and review records are protected. The host applies proposals, runs Lean, obtains a separate review, and checks for source conflicts before adoption. Worker dependencies require their prerequisite jobs to have been adopted.

SQLite claims and leases coordinate jobs. Retries and resumed jobs retain their history and usage. Budget reservations control subsequent calls; the worker's USD values are local estimates, not billing records or a guaranteed per-call spending cap. Detailed worker behavior is documented in the [Japanese README](docs/README.ja.md) and [architecture guide (Japanese)](docs/architecture.md).

## Reproducible source archives

```sh
python3 tools/jonnylean.py release status
python3 tools/jonnylean.py release build artifacts/JonnyLean-v4.zip
python3 tools/jonnylean.py release check artifacts/JonnyLean-v4.zip
```

Archive creation requires current successful mechanical checks and AI reviews for every task. It packages source, specifications, contracts, documentation, reviews, and deduplicated audit evidence. Build outputs, Git history, and worker job history are excluded. Existing output files are not overwritten.

File order, timestamps, and permissions are fixed for byte reproducibility in the same Python/zlib environment. `release check` verifies archive integrity without extracting files or running code; it does not authenticate the author or re-prove the theorems. Extract the archive and run `python3 tools/jonnylean.py run all --jobs 4` inside `source/` for fresh verification. See the [operations guide (Japanese)](docs/platform.md) for limits and digest checking.

## Development and documentation

The catalog source is `catalog/fragments/`. After adding a task, regenerate and check the registry and aggregate imports:

```sh
python3 tools/jonnylean.py catalog sync
python3 tools/jonnylean.py catalog check
python3 -m unittest discover -s tests -v
```

Tests exercise valid and rejected proofs, axiom policy, stale reviews, concurrent changes, dependency planning, worker budgets and retries, adoption conflicts, and archive integrity. Synthetic AI fixtures run only in disposable test copies and are distinct from the project's review records. GitHub Actions is configured to verify tasks, run tests, and package evidence.

Detailed documentation is currently in Japanese:

- [Contributing](CONTRIBUTING.md)
- [Architecture](docs/architecture.md)
- [Operations, parallel checks, and archives](docs/platform.md)
- [Mathematics examples](docs/mathematics.md)
- [Task index and roadmap](roadmaps/elementary.md)
- [Review criteria](reviews/rubric.md)
- [Validation history](docs/validation.md)
