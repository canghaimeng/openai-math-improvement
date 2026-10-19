# Exact Fourier transforms with a larger exponent saving

Developed with [Euler](https://github.com/canghaimeng/Euler), a mathematical research system for collaborative reasoning and human-guided exploration.

**[Read the paper](paper.pdf)**

For every positive transform length, we obtain

$$T(n)=O\!\left(n(\log n)^{1-63/50000}\right).$$

The saving **0.00126** improves OpenAI's original all-length saving **10⁻¹³** in the specified exact complex-arithmetic model. Preparation, indexing and movement are included.

The proof combines an explicit finite tensor construction, a recursive schedule with charged workspace, and the transfer to arbitrary Fourier lengths. It builds on OpenAI's reductions and the community complex588 construction.

[Lean sources](lean/) · [Verified submission](https://github.com/bigospeedrun/verifier/issues/16#issuecomment-6240050032)

Build the formalization from `lean/`:

```sh
lake exe cache get
lake build
lake env lean Check.lean
```

[Explore Euler](https://github.com/canghaimeng/Euler) · [Project website](https://canghaimeng.site/euler/?lang=zh)
