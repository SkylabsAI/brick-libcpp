# Review artifacts — `std::optional<unsigned char>`

This packet presents a small, representative slice of one
specification-pipeline run for focused source review.

Everything is under `spec-review/` and is wired into no Dune rule, so it cannot
affect `rocq-brick-libstdcpp/`.

This packet deliberately contains the complete semantic specification but only
three of the run's client/proof pairs. The proof-automation implementation,
remaining clients, proof obligations, mutations, and execution records are
available separately; they are not needed for the initial judgement requested
here.

## Reading order

| Path | What to review |
|---|---|
| `1-scope.md` | The exact API surface and the three selected examples |
| `spec/model.v` | The abstract empty/engaged state |
| `spec/pred.v` | The concrete libstdc++ 12 representation predicate |
| `spec/spec.v` | The six registered operation contracts |
| `spec/inc_optional.cpp` | The concrete template instantiations used for binding generation |
| `clients/positive/` | Two clients whose verification must succeed |
| `clients/negative/` | One invalid client whose verification must fail |
| `proofs/positive/` | The two corresponding proofs ending in `Qed.` |
| `proofs/negative/` | The expected-failure proof committed with `Fail Qed.` and `Abort.` |

There are ten substantive source files: four library files, three C++
clients, and three Rocq proofs.

## What feedback would help

The requested judgement is narrow:

- Is the abstract state and concrete representation the right shape for this
  specialization?
- Do the six contracts express the intended ownership, value, and lifetime
  behavior?
- Are the representation and contract definitions idiomatic for this
  repository?
- Do the three selected proofs demonstrate useful consequences of the spec,
  rather than merely restating it?

No assessment of the pipeline, mutation campaign, or PBT harness is requested
in this PR.

## Validation

`SHA256SUMS` records the identities of the files in this packet.

The complete optional proof family was checked with:

```text
agent-foundation-devcontainer-cmake-3.30.9-v2:latest
sha256:7991a877c5297c564a524a4b3e3e6f260cc69d7ab0c4e23bf4ebc3e8f9d1c63f
opam exec -- dune build -j 32 @proof/optional/all @test/optional/all
```

The build exited 0 and produced all 23 optional proof objects. The proof
automation implementation and generated binding files are intentionally
omitted from this focused source review.

## Deliberate omissions

The completed run contains nineteen positive scenarios, six adversarial probes,
and eleven commissioned proof obligations. This packet selects only:

- ordinary construction and observation;
- snapshot ownership after changing the constructor source; and
- rejection of a reference that outlives the optional.

The smaller packet is intended to make the core design reviewable without
asking a maintainer to audit every generated evidence artifact.
