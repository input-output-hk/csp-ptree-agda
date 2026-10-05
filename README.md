# csp-ptree-agda

A library mechanising Communicating Sequential Processes (CSP) in Agda, based on Process Trees (PTrees), an extension of Interaction Trees for process algebra.

The semantic model is a single coinductive process tree type, `PTree E I R`, rather than a bespoke transition system. Its only branching node, `react`, fuses a visible offer map (external choice over events) with a silent τ-branch map (internal nondeterministic choice). Because one node can both offer visible events and have an enabled τ, the model directly expresses sliding/timeout states, which separate visible and branching nodes cannot.

On top of this type the library develops, generically and independently of CSP:

- strong, weak, and divergence-respecting weak bisimulation;
- stable refusals and stable failures;
- the failures-divergences model, with its refinement orders and equivalence, and bridges from bisimulation to failures-divergences equivalence;
- linear-time temporal logic over process trees.

The CSP layer defines the usual operators (prefix, external and internal choice, sliding, parallel and interleaving, hiding, renaming, sequential composition, throw, interrupt, priority, ...) as functions over process trees and proves their algebraic laws, mainly in the failures-divergences model. Worked examples include case studies from Roscoe's *The Theory and Practice of Concurrency* and *Understanding Concurrent Systems*, dining philosophers, and a vending machine.

A probabilistic extension of the process tree model is planned.

## Quick start

With Agda 2.8.0 and the `standard-library` and `standard-library-classes` libraries installed, run `agda src/CSP/Operators.agda` from the repository root.

See [src/README.md](src/README.md) for build details, the module structure, and conventions.
