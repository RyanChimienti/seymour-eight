# Seymour's Second Neighborhood Conjecture through minimum outdegree eight

This is an AI-generated Lean proof of Seymour's Second Neighborhood Conjecture for graphs having a vertex whose outdegree is at most eight. It assumes the result through outdegree seven, which is established in [Sadhukhan et al. (2026)](https://arxiv.org/abs/2606.30588).

The statement of the theorem is in `SeymourEight.lean`, using the definitions in `Definitions.lean`.

See [`formalization.yaml`](./formalization.yaml) for complete details.

## Building the project

The project must be built with a limited number of threads to avoid exhausting the available RAM. Use 1 thread per 16GB of available RAM. (With significantly less than 16GB of RAM, it will not build.) For example, on Ubuntu with 16GB of RAM, run this command in the repository root:

```sh
LEAN_NUM_THREADS=1 lake build
```

At 1 thread, the build should complete in ~5.5 hours.

The build will create ~51 GiB of build artifacts in the `.lake` folder, so you'll also need that much free disk space.
