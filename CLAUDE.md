# CMAbelianVarieties: instructions for Claude Code

## About the project
A Lean 4 + Mathlib formalisation of CM abelian varieties. The goal is to prove
that a CM abelian variety over an algebraically closed field of characteristic 0
(together with its CM structure) has a model over a number field. The statement
lives in `CMAbelianVarieties/Theorem.lean` (not yet proven).

## Ground rules
- **Do NOT edit, create, move or delete any file unless I specifically tell you
  to.** If you think a change would help, describe it and suggest it instead.
  An explicit task (e.g. "run the checklist") permits only the edits that task covers.
- Do not commit or push unless I ask (or the checklist tells you to).
- If you write a proof or definition, mark it with a comment directly above it
  saying it was written by AI (see "AI usage" in README.md).

## `to claude` comments
- I sometimes leave instructions for you as comments in the code, of the form
  `-- to claude: ...` (spacing and capitalisation may vary, e.g. `to claude : ...`).
- Do not act on them by yourself. Only act when I tell you to execute a
  `to claude` command.
- When I do, first search every file of the project (excluding `.lake/` and
  `.git/`) for all `to claude` comments, case-insensitively:
      grep -rni "to claude" --exclude-dir=.lake --exclude-dir=.git .
  - If there is more than one, do NOT execute any of them. Inform me, listing
    each one with its file and line.
  - If there is exactly one, follow it. Executing it counts as permission to make
    the edits that instruction asks for (and only those).
  - Once it has been executed, delete the `to claude` comment itself.

## Building
- Lean toolchain and Mathlib version: see `lean-toolchain` / `lakefile.toml`.
- Build everything: `lake build`
- Build one module: `lake build CMAbelianVarieties.Path.To.File`
- Regenerate `CMAbelianVarieties.lean` (imports every library file): `lake exe mk_all`
- `relaxedAutoImplicit = false` and the Mathlib standard linter set are enabled.

## Layout
- `CMAbelianVarieties/`: the library
  - `Defn.lean`, `Theorem.lean`: main definitions and the main theorem
  - `AbstractNonsense/`: category theory (group objects, pullbacks, End rings)
  - `AlgebraicGeometry/`: schemes, Lie algebras, abelian varieties, homomorphisms
  - `preCMType/`: pre-CM types and field representations
  - `ForMathlib/`: results that could be upstreamed to Mathlib
  - `Catalogue.lean` files: `#check` cheat sheets, not real content
- `Test/`: scratch/test files, outside the library (not imported by mk_all)
- `Pondering/`: notes

## Bookkeeping files
- `CMAbelianVarieties/ToDo`: unfinished results (still `sorry`). Only pending
  tasks belong here; completed tasks are removed.
- `MindMap.md`: Mermaid diagram of imports between project files.
- `ClaudeCodeChecklist`: the end-of-session checklist. When I say "run the
  checklist", follow it step by step, exactly.

## Lean conventions
- Follow Mathlib style and naming conventions.
- Keep imports minimal: import the smallest Mathlib/project file that suffices.
- When searching for Mathlib results, report the exact name and file.
