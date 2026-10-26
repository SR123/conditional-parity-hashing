STANDALONE CONDITIONAL PARITY HASHING PROOF

Compiler: Lean 4.35.0-rc2.
Mathlib: commit 065356127b1dc0016f66b7283ce0ce2c4055aa55.

Install the official elan toolchain manager, then from this folder run:
  lake update
  lake exe cache get
  lake build
  lake env python3 build_verify.py
The first two commands need network access to the pinned public sources
and Mathlib cache. The final script creates a new compilation directory
on every run, rebuilds all distributed research modules from source,
checks their hashes, and reads the axiom reports. The default Lake library target includes all flat source modules, with
Verification importing the final theorem and both extensions.
No compiled research objects or downloaded dependencies are distributed.

Expected success:
  FULL_MAIN_THEOREM_KERNEL_CHECKED in build/latest_verification.json
  certified_main axioms: propext, Classical.choice, Quot.sound
The order of the three names can differ. The script rejects other axioms,
unchecked proof placeholders and changes to any manifested source.
Run times depend strongly on the local dependency cache; allow several
minutes once the cache is available. No duration guarantee is made.

An existing pinned public Mathlib dependency cache can be reused:
  python3 build_verify.py --lean /absolute/path/to/pinned/lean \
    --dependency-project /absolute/path/to/pinned/lake/project
Only that project's .lake/packages dependency libraries are read. Its
compiled research outputs are explicitly excluded from LEAN_PATH.

STATEMENT MAP
CertifiedMain.lean: ConditionalParityHashing.certified_main proves the
complete closed rate interval, positive denominator, exact rational score
box and existence of a finite law with signed score below -0.09738.
SixThresholdCriterion.lean: the six full-pair tests imply the four
singleton tests, hence the general parity-subtraction criterion.
ParitySemanticBridge.lean: actual simultaneous finite-coordinate
approximation and exact source masses.
FiniteLaw.lean: finite Shannon entropy in bits. FiniteLaw4 m is a law on
(Fin m)^4; m is an alphabet size, not the block length.
AlmostEntropicClosure.lean: the genuine topological closure of finite
entropy vectors. No outer cone substitutes for this closure.
ParityCandidate.lean: paperJ has the paper's CD|A, CD|B, AB, CD orientation.
The inherited finiteJ/tableJ definitions have another orientation and are
not the definitions used for the main score.

PACKAGE CLEANUP
This release retains 27 proof modules plus Verification.lean. The earlier
Gaussian/stability import chain and unrelated unproved proposition
FiniteUniversalUpper are omitted. The namespace SharpStability is kept
only as a compatibility name for foundational definitions; it introduces
no stability assumption. The basic closure definitions/inclusion lemmas
are unchanged; unrelated results were removed from that module. The
main theorem and all other retained mathematical source files are
unchanged. The standalone cleanup was rebuilt from source; the complete report and
per-module logs are recorded in evidence/.

SCOPE
The main theorem, generic ten-threshold proof, six-test reduction and
closure/source semantic bridges are formalised. The finite conditional
sampler and fixed-path endpoint argument
are written proofs rather than separate Lean declarations. The formal
finite-law conclusion follows by closure and continuity.
