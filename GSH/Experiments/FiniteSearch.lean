import GSH.Certificates.RegexCertificate

/-!
# Experiment metadata

Search output is intentionally kept outside the trusted theorem layer.  A run
must carry resource bounds and hashes; only checked certificates cross into
mathematical claims.
-/

set_option autoImplicit false

namespace GSH

structure SearchManifest where
  approachId : String
  commit : String
  inputSha256 : String
  outputSha256 : String
  stateBound : Nat
  expressionSizeBound : Nat
  wallClockSeconds : Nat
  deriving Repr

end GSH
