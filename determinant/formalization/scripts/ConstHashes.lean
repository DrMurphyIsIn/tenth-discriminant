import CN1.Finite.Bridge
import CN1.Finite.Converse
import CN1.Finite.Elementary
import CN1.Finite.Params
import CN1.Finite.SplitPrime
import CN1.Finite.Witnesses
import CN1.Finite.Witnesses.Chunk1
import CN1.Finite.Witnesses.Chunk2
import CN1.Finite.Witnesses.Chunk3
import CN1.Finite.Witnesses.Chunk4
import CN1.Foundations.Basic
import CN1.Foundations.Character
import CN1.Foundations.Discr
import CN1.Foundations.Ramified
import CN1.Foundations.Splitting
import ELEM.Count
import ELEM.Count.AuxPrime
import ELEM.Count.Lattice
import ELEM.Count.Partial
import ELEM.Count.SplitBound
import ELEM.Defs
import ELEM.Divisibility
import ELEM.Divisibility.Count
import ELEM.Divisibility.Det
import ELEM.Divisibility.Main
import ELEM.Divisibility.Rows
import ELEM.Endpoint
import ELEM.Endpoint.Comparison
import ELEM.Endpoint.Monotone
import ELEM.Frobenius
import ELEM.Glue
import ELEM.Hypotheses
import ELEM.Main
import ELEM.Nonvanishing.Hermite
import ELEM.Nonvanishing.Main
import ELEM.Nonvanishing.Minor
import ELEM.Nonvanishing.Params
import ELEM.Primes
import ELEM.Primes.LemmaTwo
import ELEM.Primes.Mertens
import ELEM.Primes.Numerics
import ELEM.Primes.SumLogDivSq
import ELEM.Primes.Theta
import ELEM.Sieve.Chunk0
import ELEM.Sieve.Chunk1
import ELEM.Sieve.Chunk2
import ELEM.Sieve.Chunk3
import ELEM.Sieve.Chunk4
import ELEM.Sieve.Chunk5
import ELEM.Sieve.Chunk6
import ELEM.Sieve.Chunk7
import ELEM.Sieve.Defs
import ELEM.Sieve.Main
import ELEM.Sieve.Range
import ELEM.Size.Bound
import ELEM.Size.Embedding
import ELEM.Size.Leibniz

/-! Prints, for every constant declared in a module of `ELEM` or `CN1`, its module, name, kind,
universe parameters, and the structural hashes of its type and value. Written to the file given by
the environment variable `HASH_OUT`. -/

open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let mut lines : Array String := #[]
  for (n, ci) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? n then
      let m := env.header.moduleNames[idx.toNat]!
      if (`ELEM).isPrefixOf m || (`CN1).isPrefixOf m then
        let kind := match ci with
          | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "thm"
          | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot" | .inductInfo _ => "induct"
          | .ctorInfo _ => "ctor" | .recInfo _ => "rec"
        let v := match ci.value? (allowOpaque := true) with
          | some v => toString v.hash
          | none => "-"
        lines := lines.push s!"{m} {n} {kind} {ci.levelParams} {ci.type.hash} {v}"
  let out := (← IO.getEnv "HASH_OUT").getD "hashes.txt"
  IO.FS.writeFile out (String.intercalate "\n" (lines.qsort (· < ·)).toList ++ "\n")
  IO.println s!"constants: {lines.size}"
