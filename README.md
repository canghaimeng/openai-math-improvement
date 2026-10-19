<div align="center">

# Euler · Beyond the Published Bounds

**English** · [简体中文](README.zh-CN.md)

### Publicly accessible models. Collaborative mathematical progress.

[**Euler Code**](https://github.com/canghaimeng/Euler) · [**Project Website**](https://canghaimeng.site/euler/?lang=en) · [**Technical Report**](https://arxiv.org/abs/2610.19864)

</div>

**20 problems tested · 8 improved results · 3 community-leading results**

We tested **[Euler](https://github.com/canghaimeng/Euler)** on 20 problems from OpenAI's mathematics release. Teams of publicly accessible models obtained results that improve the original published bounds on **8 problems**. **Three results surpassed the strongest community bounds we verified in our October 17–19, 2026 comparison.**

These results show how Euler's shared research state and coordinated agent teams can take publicly accessible models beyond specific mathematical results reported by OpenAI's internal research models. The exact Fourier-transform result also comes with a complete Lean proof.

Euler turns an agent team's exploration into a shared mathematical research state. Models build on one another's arguments, track proof dependencies, preserve useful failed attempts, and submit claims for independent checking. Researchers can follow the evolving proof graph and guide the team from saved research states.

## Mathematical results

**Average reasoning time: 86 minutes per problem.**

| Problem | Result developed with Euler | Reasoning time | Paper and idea |
| --- | --- | --- | --- |
| **Exact discrete Fourier transform** ⭐ | Exponent saving **63/50000 = 0.00126**, improving the original all-length saving **10⁻¹³**. Complete Lean formalization included. | 3 h 27 min | [Read →](problems/bound-130/) |
| **Cylinder covers of a regular tetrahedron** ⭐ | **20,000 cylinders** with smaller total base area than OpenAI's displayed **16,000,000-cylinder** construction. | 1 h 26 min | [Read →](problems/bound-100/) |
| **Spherical Laughlin spectral gap** ⭐ | Exact eventual gap bound **0.21901701265**, over **5.47 times** the original uniform bound **1/25**. | 2 h 1 min | [Read →](problems/bound-269/) |
| **Switch-chain mixing** | Mixing-time bound **n⁶**, improving the original **2n⁸** bound for the same four-vertex proposal chain. | 35 min | [Read →](problems/bound-131/) |
| **Average sensitivity** | Uniform coefficient **3.192**, improving OpenAI's coefficient **8** in the bound `AS(f) ≤ C d√n`. | 2 h 22 min | [Read →](problems/bound-127/) |
| **One-sample matroid prophet inequalities** | An explicit rational guarantee exceeding the original **2⁻²⁹³** in the full-seed adversary model. | 43 min | [Read →](problems/bound-111/) |
| **Sensitivity versus block sensitivity** | An explicit separation exponent **α > 2.032083**, improving the original displayed construction. | 20 min | [Read →](problems/bound-132/) |
| **Heilbronn triangle problem** | Explicit exponent increment **η = 2/100866719** in the lower bound `c n^(-2+η)` for every sufficiently large `n`. | 38 min | [Read →](problems/bound-191/) |

⭐ **Community-leading:** these three results exceed the best comparable public bounds checked in the October 17–19, 2026 comparison.

Each paper states the mathematical model, assumptions, construction and proof, with credit to the original work and subsequent contributions. The collection builds on those ideas to obtain the displayed results.

### A complete formal result

The exact DFT theorem is accompanied by [Lean source](problems/bound-130/lean/) and has passed **Lean and nanoda verification** through [Big O Speedrun](https://github.com/bigospeedrun/verifier/issues/16#issuecomment-6240050032).

```math
T(n)=O\!\left(n(\log n)^{1-63/50000}\right).
```

## Explore with Euler

Bring a mathematical question, configure your model team, and follow the investigation as it develops. Euler combines long-running collaboration, a live proof graph, and recoverable research milestones so that useful progress remains available for the next step.

**[Start with Euler →](https://github.com/canghaimeng/Euler)**

Across **20 mathematical problems** from OpenAI’s release, Euler teams obtained improved bounds or constructions on **8 problems**, with **3 results exceeding the best comparable community results checked in this study**. Through shared research state, team collaboration and independent verification, publicly accessible models can advance specific mathematical results published by internal research models.

For research collaboration: **canghaimeng@sjtu.edu.cn**.
