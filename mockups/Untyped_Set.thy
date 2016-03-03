theory Untyped_Set
imports Main
begin

section {* Untyped Set Theory as in TLA+ *}

subsection {* Basic Setup *}

definition The_bang :: "('a \<Rightarrow> bool) \<Rightarrow> 'a" where
  "The_bang P = (if \<exists>x. P x then The P else Nitpick.unknown)"


subsection {* Set Membership *}

typedecl u

text \<open>
Declare @{typ u} with an "infinite" annotation in Nunchaku, to exploit its
approximation of quantifiers and polarity analysis?

Issue: Lack of precision. Model "proto"?
\<close>

nitpick_params [user_axioms, dont_box, show_all, atoms u = a b c d e f g h i j k l]

axiomatization
  emptyset :: u and
  mem :: "u \<Rightarrow> u \<Rightarrow> bool" (infix "\<in>#" 50)
where
  emptyset: "\<And>x. \<not> x \<in># emptyset" and
  mem_ext: "\<And>A B. A = B \<or> (\<exists>x. \<not> (x \<in># A \<longleftrightarrow> x \<in># B))" and
  mem_acyclic: "\<And>A. \<not> tranclp (op \<in>#) A A"

nitpick_params [card = 1-8, eval = "\<lambda>x. {y. y \<in># x}", format mem = 2]

lemma "x \<in># A"
  nitpick [expect = genuine]
  oops

lemma "\<not> x \<in># A"
  nitpick [expect = genuine]
  oops

lemma "x \<in># x"
  nitpick [expect = genuine]
  oops

lemma "\<not> x \<in># x"
  nitpick [expect = none]
  sorry

lemma "x \<in># y \<Longrightarrow> \<not> y \<in># x"
  nitpick [expect = none]
  sorry

lemma "x \<in># y \<Longrightarrow> y \<in># z \<Longrightarrow> \<not> z \<in># x"
  nitpick [expect = none]
  sorry


subsection {* Subset *}

definition
  subseteq :: "u \<Rightarrow> u \<Rightarrow> bool" (infix "\<subseteq>#" 50)
where
  "subseteq A B \<longleftrightarrow> (\<forall>x. x \<in># A \<longrightarrow> x \<in># B)"


subsection {* Functions *}

axiomatization
  dom :: "u \<Rightarrow> u" and
  app :: "u \<Rightarrow> u \<Rightarrow> u" (infixl "\<cdot>" 70)
where
  app_ext: "\<And>A B. dom A = dom B \<and> (\<forall>x. x \<in># dom A \<longrightarrow> f \<cdot> x = g \<cdot> x) \<longrightarrow> f = g"

abbreviation mapsto :: "u \<Rightarrow> (u \<Rightarrow> u) \<Rightarrow> u" where
  "mapsto A f \<equiv> The_bang (\<lambda>g. dom g = A \<and> (\<forall>x. x \<in># A \<longrightarrow> g \<cdot> x = f x))"

lemma "f = mapsto (dom f) (op \<cdot> f)"
  nitpick [expect = none]
  sorry


subsection {* Powerset *}

definition
  Pow :: "u \<Rightarrow> u"
where
  "Pow B = The_bang (\<lambda>C. \<forall>A. A \<in># C \<longleftrightarrow> A \<subseteq># B)"

lemma "A \<in># Pow B"
  nitpick [expect = genuine]
  oops

lemma "\<not> A \<in># Pow B"
  nitpick [expect = genuine]
  oops

lemma "A \<in># Pow A"
  nitpick [expect = none]
  sorry

lemma "A \<subseteq># Pow A"
  nitpick [expect = genuine]
  oops


subsection {* Big Union *}

definition
  Union :: "u \<Rightarrow> u"
where
  "Union B = The_bang (\<lambda>C. \<forall>x. x \<in># C \<longleftrightarrow> (\<exists>A. x \<in># A \<and> A \<in># B))"

lemma "A \<in># Union A"
  nitpick [expect = genuine]
  oops

lemma "\<not> A \<in># Union A"
  nitpick [expect = none]
  sorry

lemma "A = Union (Pow A)"
  nitpick [expect = none]
  sorry

end
