```lean
import GlimpseOfLean.Library.Basic
```

# 含义

## 使用蕴含关系

Lean 使用符号 `→` 表示蕴含关系，而不是 `⇒`，因为它将 `P → Q` 的证明视为一个将任何 `P` 的证明映射到 `Q` 的证明的函数
（如果您无法看到 `→` 和 `⇒` 之间的区别，请增大字体大小）。

例如，给定实数 `a`，引理 `sq_pos_of_pos` 声明 `0 < a → 0 < a^2`，因此下面的证明将“函数” `sq_pos_of_pos` 应用于假设 `ha`。

```lean
example (a : ℝ) (ha : 0 < a) : 0 < a^2 := by {
  exact sq_pos_of_pos ha
}
```

上述证明是一个直接证明：我们已经知道 `0 < a`，并将该事实输入到蕴含关系中。
我们还可以使用 `apply` 策略进行逆向推理。

```lean
example (a : ℝ) (ha : 0 < a) : 0 < (a^2)^2 := by {
  apply sq_pos_of_pos -- 由于存在 `sq_pos_of_pos`，只需证明 `0 < a^2`
  apply sq_pos_of_pos -- 由于存在 `sq_pos_of_pos`，只需证明 `0 < a`
  exact ha -- 这正是我们的假设 `ha`
}
```

接下来的练习使用引理 `add_pos : 0 < x → 0 < y → 0 < x + y`。请注意，在应用 `add_pos` 后，您将有两个目标，您需要逐个证明。

```lean
example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 < a^2 + b^2 := by {
  sorry
}
```

您还可以用前向推理给出一个证明，使用 `have` 策略。为了宣布一个中间陈述，我们使用:

  `have my_name : my_statement`

这将触发一个新目标的出现：证明该陈述。证明需要以一个中心点 `·` 开头（使用 `\.` 输入），并且应该缩进。
证明完成后，该陈述在名为 `my_name` 的名称下可用。

```lean
example (a : ℝ) (ha : 0 < a) : 0 < (a^2)^2 := by {
  have h2 : 0 < a^2      -- 我们将 `0 < a^2` 声明为一个子目标
  · apply sq_pos_of_pos  -- 我们开始证明子目标
    exact ha             -- 此行缩进，因此是子目标的一部分的证明
  exact sq_pos_of_pos h2 -- 我们完成子目标，并使用它证明主目标。
}
```

现在使用前向推理证明与之前相同的引理。

```lean
example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 < a^2 + b^2 := by {
  sorry
}
```

## 证明蕴含关系

要证明一个蕴含关系，我们需要假设前提并证明结论。这可以使用 `intro` 策略完成。上面的练习偷偷地证明了蕴含关系 `a > 0 → (a^2)^2 > 0`，但是前提已经为我们引入。

```lean
example (a : ℝ) : a > 0 → b > 0 → a + b > 0 := by {
  intro ha hb -- 在这里您可以选择任何名称
  exact add_pos ha hb
}
```

现在证明以下简单的命题逻辑命题。
注意，`p → q → r` 的意思是 `p → (q → r)`。

```lean
example (p q r : Prop) : (p → q) → (p → q → r) → p → r := by {
  sorry
}
```

# 等价性

## 使用等价性重新写入命题

在前面的文档中，我们看到了如何使用等式进行重写。
数学命题的类似操作是使用等价关系进行重写。这也可以使用 `rw` 策略完成。
Lean 使用 `↔` 表示等价关系，而不是 `⇔`（如果您无法看到区别，请增大字体大小）。

在接下来的练习中，我们将使用引理：

  `sub_nonneg : 0 ≤ y - x ↔ x ≤ y`

```lean
example {a b c : ℝ} : c + a ≤ c + b ↔ a ≤ b := by {
  rw [← sub_nonneg]
  have key : (c + b) - (c + a) = b - a -- 这里我们引入一个名为 key 的中间陈述
  · ring   -- 并在 `·` 之后证明它
  rw [key] -- 现在我们可以使用 `key`。这个 `rw` 使用了一个等式结果，而不是等价关系
  rw [sub_nonneg] -- 然后切换回等价关系以达到命题 a ≤ b ↔ a ≤ b
}
```

让我们证明一个变种

```lean
example {a b : ℝ} (c : ℝ) : a + c ≤ b + c ↔ a ≤ b := by {
  sorry
}
```

上述引理已经在数学库中，名称为 `add_le_add_iff_right`：

`add_le_add_iff_right (c : ℝ) : a + c ≤ b + c ↔ a ≤ b`

这可以解读为：“`add_le_add_iff_right` 是一个函数，它将一个实数 `c` 作为输入
其中，这个引理将 “具有类型为 `T` 的值作为输入，并输出 `a + c ≤ b + c ↔ a ≤ b` 的证明。”以下是使用此引理的示例。

```lean
example {a b : ℝ}  (ha : 0 ≤ a) : b ≤ a + b := by {
  calc
    b = 0 + b := by ring
    _ ≤ a + b := by { rw [add_le_add_iff_right b] ; exact ha  }
}
```

## 将等价关系视为两个蕴含关系的组合

在上述证明的第二行有点愚蠢：我们使用语句重写将目标减少到假设 `ha`，但将等价关系视为双重蕴含可能更自然。我们可以将等价关系 `h : P ↔ Q` 的两个蕴含关系表示为 `h.1 : P → Q` 和 `h.2 : Q → P`。这样可以将上述证明重写为：

```lean
example {a b : ℝ}  (ha : 0 ≤ a) : b ≤ a + b := by {
  calc
    b = 0 + b := by ring
    _ ≤ a + b := by exact (add_le_add_iff_right b).2 ha
}
```

让我们使用 `add_le_add_iff_left a : a + b ≤ a + c ↔ b ≤ c` 进行一个变种。

```lean
example (a b : ℝ) (hb : 0 ≤ b) : a ≤ a + b := by {
  sorry
}
```

## 证明等价关系

要证明一个等价关系，可以使用 `rw`，直到目标变成重言式 `P ↔ P`，就像处理等式一样。

也可以使用 `constructor` 策略分别证明两个蕴含关系。

下面是一个例子。

```lean
example (a b : ℝ) : (a-b)*(a+b) = 0 ↔ a^2 = b^2 := by {
  constructor
  · intro h
    calc
      a ^ 2 = b^2 + (a - b) * (a + b)  := by ring
          _ = b^2 + 0                  := by rw [h]
          _ = b^2                      := by ring
  · intro h
    calc
      (a-b)*(a+b) = a^2 - b^2  := by ring
                _ = b^2 - b^2  := by rw [h]
                _ = 0          := by ring
  }
```

您可以在此练习中尝试自己操作。

```lean
example (a b : ℝ) : a = b ↔ b - a = 0 := by {
  sorry
}
```

这就是本文档的结尾，您在其中了解了如何处理蕴含关系和等价关系。
在这个文档中，您学到了以下策略：
* `intro`：引入前提假设或变量。
* `apply`：应用一个定理或引理来生成子目标。
* `have`：声明一个中间陈述，并为该陈述生成一个子目标。
* `constructor`：将等价关系分解为两个蕴含关系，并分别生成对应的子目标。

这些策略是在 Lean 证明中常用的工具，它们可以帮助您构建您的证明过程。
