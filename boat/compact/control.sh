#!/usr/bin/env bash
# In a disposable Linux VM, exercise the production linking and kernel checks on a tiny interface.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
prefix=$(lean --print-prefix)
fixture=$(mktemp -d /opt/riemann-compact-control.XXXXXXXX)
trap 'rm -rf -- "$fixture"' EXIT
chmod 755 "$fixture"
cd "$fixture"
mkdir matcher
cp "$here/CompareOnly.lean" matcher/
cp "$here/matchrunner.toml" matcher/lakefile.toml
(cd matcher && lake build matchrunner)
mkdir -p runtime/{interface,foundation,compat,checker,deps/zeta} prepared/comparator/{ChallengeDeps,Challenge,Solution}
cp matcher/.lake/build/bin/matchrunner runtime/checker/
echo 'def fixtureValue : Nat := 1' > runtime/deps/zeta/ChallengeDeps.lean
(cd runtime/deps/zeta && lean -o ChallengeDeps.olean ChallengeDeps.lean)
echo 'import Init' > runtime/compat/LegacyFinsetSyntax.lean
(cd runtime/compat && lean -o LegacyFinsetSyntax.olean LegacyFinsetSyntax.lean)
printf 'axiom fixtureRH : True\ntheorem riemannHypothesis : True := fixtureRH\n' > runtime/interface/Main.lean
printf 'theorem fixtureRH : True := True.intro\ntheorem riemannHypothesis : True := fixtureRH\n' > runtime/foundation/Main.lean
for m in interface foundation; do (cd runtime/$m && lean -o Main.olean Main.lean); done
echo 'import ChallengeDeps
import Main' > prepared/comparator/ChallengeDeps/CandidateSpec.lean
for kind in Challenge Solution; do
  { echo 'import ChallengeDeps.CandidateSpec'
    for n in candidate_strict_improvement candidate_critical_line_bound candidate_critical_line_bound_cumulative; do
      echo "theorem $n : True := riemannHypothesis"
    done
  } > prepared/comparator/$kind/Candidate.lean
done
chmod -R a+rX,go-w runtime prepared
bash "$here/run-job.sh" "$PWD/prepared" "$PWD/runtime" "$prefix" 12G "$PWD/pass.json"
cp prepared/comparator/Solution/Candidate.lean original.lean
sed -i 's/candidate_critical_line_bound : True := riemannHypothesis/candidate_critical_line_bound : 1 = 1 := rfl/' prepared/comparator/Solution/Candidate.lean
if bash "$here/run-job.sh" "$PWD/prepared" "$PWD/runtime" "$prefix" 12G "$PWD/wrong.json"; then exit 30; fi
sed 's/candidate_critical_line_bound : True := riemannHypothesis/candidate_critical_line_bound : True := by sorry/' original.lean > prepared/comparator/Solution/Candidate.lean
if bash "$here/run-job.sh" "$PWD/prepared" "$PWD/runtime" "$prefix" 12G "$PWD/extra.json"; then exit 31; fi
test -f pass.json && test ! -e wrong.json && test ! -e extra.json
