import Generated.Commitment.Funs
import Examples.CommitmentScheme.Common

/-!
Import checkpoint for the educational byte-sized commitment.

No implementation refinement or security theorem is claimed here.
A later refinement requires successful hash calls interpreted by one
fixed function of message and salt. The Rust immutable receiver does
not establish that contract. Uniformity of RNG outputs is separate.
-/

#check CMOracle
#check CMCommit
#check CMCheck
