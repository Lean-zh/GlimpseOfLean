# Lean 快速入门

[中文](README.zh.md) | [English](README.md)

本仓库为希望快速了解 Lean 定理证明的读者提供了一个入门介绍。目标是在 2 到 3 小时内感受一下在 Lean 中进行证明的样子，或者花费半天到一整天的时间来学习。

这里有两条学习路径，都从阅读 `Introduction.lean` 文件开始。短路径会继续到 `Shorter.lean` 文件，如果你准备快速学习，这个文件可以让你在两小时内接触到非平凡的数学证明。

如果你有更多时间，你应该阅读 `Basics` 文件夹中的说明并完成练习，然后选择 `Topics` 文件夹中的一个文件进行学习。当然，如果你有更多时间，你可以学习该文件夹中的所有文件。

要使用 Lean，你需要在本地安装 Lean，或使用 lean4web 服务器，或使用 Codespaces 或 Gitpod。

## 在线版本，无需注册

如果你不想安装 Lean 且不想在任何网站创建账户，你可以使用 [Lean FRO](https://lean-fro.org/) 托管的 [lean4web 服务器](https://live.lean-lang.org/)。或者在 [Lean-ZH](https://leanprover.cn/) 托管的 [lean4web](https://live.leanprover.cn/) 上进行学习。

步骤如下：

* 阅读[介绍文件](https://live.lean-lang.org/#project=GlimpseOfLean&url=https%3A%2F%2Fraw.githubusercontent.com%2FPatrickMassot%2FGlimpseOfLean%2Frefs%2Fheads%2Fmaster%2FGlimpseOfLean%2FIntroduction.lean)
* 如果选择短路径，阅读和完成[说明和练习文件](https://live.lean-lang.org/#project=GlimpseOfLean&url=https%3A%2F%2Fraw.githubusercontent.com%2FPatrickMassot%2FGlimpseOfLean%2Frefs%2Fheads%2Fmaster%2FGlimpseOfLean%2FExercises%2FShorter.lean)。

如果你想选择长路径，相关链接如下：
* [01Rewriting](https://live.lean-lang.org/#project=GlimpseOfLean&url=https%3A%2F%2Fraw.githubusercontent.com%2FPatrickMassot%2FGlimpseOfLean%2Frefs%2Fheads%2Fmaster%2FGlimpseOfLean%2FExercises%2F01Rewriting.lean)
* [02Iff](https://live.lean-lang.org/#project=GlimpseOfLean&url=https%3A%2F%2Fraw.githubusercontent.com%2FPatrickMassot%2FGlimpseOfLean%2Frefs%2Fheads%2Fmaster%2FGlimpseOfLean%2FExercises%2F02Iff.lean)
* [03Forall](https://live.lean-lang.org/#project=GlimpseOfLean&url=https%3A%2F%2Fraw.githubusercontent.com%2FPatrickMassot%2FGlimpseOfLean%2Frefs%2Fheads%2Fmaster%2FGlimpseOfLean%2FExercises%2F03Forall.lean)
* [04Exists](https://live.lean-lang.org/#project=GlimpseOfLean&url=https%3A%2F%2Fraw.githubusercontent.com%2FPatrickMassot%2FGlimpseOfLean%2Frefs%2Fheads%2Fmaster%2FGlimpseOfLean%2FExercises%2F04Exists.lean)

这些是基础内容。然后你可以根据自己的数学兴趣选择：
* [SequenceLimits](https://live.lean-lang.org/#project=GlimpseOfLean&url=https%3A%2F%2Fraw.githubusercontent.com%2FPatrickMassot%2FGlimpseOfLean%2Frefs%2Fheads%2Fmaster%2FGlimpseOfLean%2FExercises%2FTopics%2FSequenceLimits.lean) 学习实数序列的基本性质。
* [RingTheory](https://live.lean-lang.org/#project=GlimpseOfLean&url=https%3A%2F%2Fraw.githubusercontent.com%2FPatrickMassot%2FGlimpseOfLean%2Frefs%2Fheads%2Fmaster%2FGlimpseOfLean%2FExercises%2FTopics%2FRingTheory.lean) 学习一些交换代数，直到交换环中的中国剩余定理。
* [Probability](https://live.lean-lang.org/#project=GlimpseOfLean&url=https%3A%2F%2Fraw.githubusercontent.com%2FPatrickMassot%2FGlimpseOfLean%2Frefs%2Fheads%2Fmaster%2FGlimpseOfLean%2FExercises%2FTopics%2FProbability.lean) 学习一些概率论。

* [GaloisAdjunctions](https://live.lean-lang.org/#project=GlimpseOfLean&url=https%3A%2F%2Fraw.githubusercontent.com%2FPatrickMassot%2FGlimpseOfLean%2Frefs%2Fheads%2Fmaster%2FGlimpseOfLean%2FExercises%2FTopics%2FGaloisAdjunctions.lean) 学习一些基础的抽象理论（有序集合间的伴随关系及其在群论和拓扑学中的应用）。

* [ClassicalPropositionalLogic](https://live.lean-lang.org/#project=GlimpseOfLean&url=https%3A%2F%2Fraw.githubusercontent.com%2FPatrickMassot%2FGlimpseOfLean%2Frefs%2Fheads%2Fmaster%2FGlimpseOfLean%2FExercises%2FTopics%2FClassicalPropositionalLogic.lean) 学习经典设定下的数理逻辑。
* [IntuitionisticPropositionalLogic](https://live.lean-lang.org/#project=GlimpseOfLean&url=https%3A%2F%2Fraw.githubusercontent.com%2FPatrickMassot%2FGlimpseOfLean%2Frefs%2Fheads%2Fmaster%2FGlimpseOfLean%2FExercises%2FTopics%2FIntuitionisticPropositionalLogic.lean) 学习直觉主义设定下的数理逻辑（如果你不了解 Heyting 代数在直觉主义逻辑中的用途，请不要尝试这个）。

在做练习时，可以参考[策略备忘单](tactics.pdf)。策略在 Lean 文件中有说明，
但 PDF 版本作为参考可能更方便。

## 在线版本，需要注册

还有一些更舒适但需要创建 [GitHub](www.github.com) 账户的网站。

* 要使用 codespaces，请确保你已登录 GitHub，点击下面的按钮，选择 `4-core`，然后按 `Create codespace`。几分钟后，一个带有 Lean 的编辑器将在你的浏览器中打开。

    [![在 GitHub Codespaces 中打开](https://github.com/codespaces/badge.svg)](https://codespaces.new/Lean-zh/GlimpseOfLean)

* Gitpod 与 Codespaces 非常相似，点击下面的按钮，按 `Continue` 并等待几分钟。

    [![在 Gitpod 中打开](https://gitpod.io/button/open-in-gitpod.svg)](https://gitpod.io/#https://github.com/Lean-zh/GlimpseOfLean)

## 本地安装

如果你想要完整的 Lean 体验，你应该在电脑上安装它。

为此，你可以按照[这里](https://leanprover-community.github.io/get_started.html)的说明进行操作。

如果你有更多时间，你应该阅读《[Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)》这本书。
