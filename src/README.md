# csp-ptree-agda: source layout

This document describes the Agda sources under `src/`: how to build them, how the modules are organised, and the conventions they follow. For a short overview of the project, see the [top-level README](../README.md).

## Requirements and build

- Agda **2.8.0** 
- `standard-library` and `standard-library-classes`, declared in the library file `csp-ptree.agda-lib` at the repository root (`include: src`)
- Typecheck any module from the repository root, e.g.:
  ```
  agda src/CSP/Operators.agda
  ```
  Agda checks imports transitively, so this is usually all you need.
- There is no Makefile; build artefacts (`.agdai`) go to `_build/` at the repository root.
- Every module uses `{-# OPTIONS --guardedness #-}`; no module uses the `NON_TERMINATING` (or `TERMINATING`) pragma.
- Some modules are literate Agda in Markdown (`.lagda.md`), mainly the worked examples under `src/CSP/Examples/`.

## Layout

The core type and the generic semantics know nothing about CSP; CSP is layered on top:

```
Process_Trees  ←  Semantics/*  ←  CSP/Operators  ←  CSP/Laws/*  ←  CSP/Examples/*
```

All paths below are relative to this directory (`src/`).

| Path | Contents |
|---|---|
| `Process_Trees.agda` | The `PTree E I R` coinductive type. `NodeKind` has three constructors: `ret` (terminal), `sil` (a single τ step), and `react v τc`, the only branching node. It fuses a visible offer map `v` with a τ-branch map `τc`, so a state can offer events and have an enabled τ at once (sliding/timeout). |
| `Classical.agda` | A single `dne` (double-negation elimination / LEM) axiom, imported only by the two `ClassicalFromLEM` certifier modules to show which postulates are "just classical logic". |
| `Semantics/` | Model-agnostic theory of process trees, parametric in `E`, `I` (see below). |
| `CSP/` | The CSP layer: operators, laws, priority, and worked examples (see below). |

### `Semantics/`: generic layer

| Module | Purpose |
|---|---|
| `LTS` | Labelled transitions (visible / τ), `⟹⟨ s ⟩` traces |
| `Bisim` / `WeakBisim` | Strong / weak bisimulation |
| `DRBisim` | Divergence-respecting weak bisimulation, `Diverges`, `deadlock` |
| `Refusals` | Stable refusals / `Offers` |
| `Failures` | Stable failures, weak reachability |
| `FailuresDivergences` | Divergences, `failures⊥`, the refinement orders `⊑F⊥`/`⊑D`/`⊑FD`, the `≈FD` equivalence |
| `StrongImpliesDR` / `DRImpliesFD` | Bridges between the bisimulation and failures-divergences theories |
| `RefinementOrders`, `Determinism`, `Expansion`, `Stability`, `TauAcc`, `FinBr`, `WeakSim`, `FailureSim`, `FDFromF`, `Deadlock`, `DeadlockDR`, `DivergenceFree`, `BisimFromRel` | Supporting lemmas and alternative characterisations for the above theories |
| `PriLTS`, `PriOrder`, `PriOrderC` | Priority-aware LTS and refinement orders (used by the priority operator) |
| `LTL/` | Linear-time temporal logic over process trees: satisfaction, weak-bisimulation invariance, fairness, refinement/trace bridges, and the classical seams they need (`ClassicalDescent`, `ClassicalFromLEM`) |

### `CSP/`: the CSP layer

| Module | Purpose |
|---|---|
| `Operators.agda` | Prefix (`⟶`), external choice (`□`), internal choice (`⊓`), sliding (`▷`), parallel (`Par`/`Par⊤`/`⦀`, alphabetised `⟦ A ∥ B ⟧`), hiding (`∖`), bind (`>>=`/`>>`), throw (`⟦ A ▷`), interrupt (`△`), replicated choice (`⨅⁺`), conditional (`◁ b ▷`), `Skip`, `Stop`, `div`, etc. Parametrised by a decidable event equality `E-≟`. |
| `Rename.agda` | Relational renaming operator |
| `Guarded.agda` | The right-hand-side constructs of the full hide-step law, defined from the hide maps so `(pchoice v) ∖ X` and the fused node agree definitionally |
| `Priority/` | The priority operator `Pri`, its channel-level variant, and biased/delayed choice combinators; `Priority/Laws/` proves its congruence, divergence, hiding, sliding and internal-choice laws |
| `Laws/` | Algebraic laws of the operators, split by proof technique: `Bisim/` (strong/weak bisimulation congruences), `FSim/` (one-way failure-simulation congruences), `FD/` (the main body: failures-divergences laws for every operator), `Traces/` (trace-level inversions and laws), `Stability/`, `DivFree/` (divergence-freedom closure), `AlphaParallel*.agda` (alphabetised parallel), `ClassicalFromLEM.agda` (certifies the FD postulates reduce to one `dne`) |
| [`Laws_status.md`](CSP/Laws_status.md) | Validation status of the algebraic laws; check here before relying on a specific law |
| `Examples/` | Worked case studies (below) |

### `CSP/Examples/`: case studies

| Path | Subject |
|---|---|
| `Example.agda`, `RenameSanity.agda`, `ThrowInterruptSanity.agda`, `PriSanity.agda`, `FSimTower.agda`, `InvariantMini.agda`, `RefinementOrderCounterexamples.agda` | Small sanity checks and counterexamples for the core theory |
| `priority/` | Basic priority, biased-choice and delayed-mux examples |
| `IO/` | A tiny IO-process example |
| `VendingMachine/` | A vending machine with LTL satisfaction and realisability examples |
| `DiningPhilosophers/` | The classic dining-philosophers problem, deadlock-freedom for `n` philosophers, and a relational-to-tree bridge |
| `TPC/` (Ch1–Ch3) | Worked examples from Roscoe's *The Theory and Practice of Concurrency* (ATM, buffers, copy, up/down counters, hiding, renaming, ...) |
| `UCS/` (Ch2–Ch9) | Ports of the FDR `ucs` example suite for Roscoe's *Understanding Concurrent Systems*, chapter by chapter (Collatz, dining philosophers variants, ABP, routing/token rings, sorting, buffers, termination/throw, an angel-of-choice model, ...) |

## Conventions

- Universe-polymorphic throughout: levels `ℓ ℓe ℓi ℓr` thread through all definitions.
- Coinductive records use the `ptree` constructor and `.force` projection.
- CSP operators are named with Unicode: `⟶` (prefix), `□` (external choice), `⊓` (internal choice), `▷` (sliding), `⦀` (interleaving), `∖` (hiding).
- No Sized Types are used to satisfy the termination/productivity checker.
- No module uses `NON_TERMINATING`; corecursive definitions are made productive directly.
- Mutually recursive definitions are written with forward-declared type signatures rather than old-style `mutual` blocks.
