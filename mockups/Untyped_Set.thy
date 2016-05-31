theory Untyped_Set
imports Main
begin
                                                    
section {* Untyped Set Theory as in TLA+ *}

subsection {* Basic Setup *}

text \<open>
Like in Nunchaku:
\<close>

definition unique_unsafe :: "('a \<Rightarrow> bool) \<Rightarrow> 'a" where
  "unique_unsafe P = (if \<exists>x. P x then The P else Nitpick.unknown)"

typedecl u
typedecl \<alpha>_mem

axiomatization
  \<gamma>1_mem :: "\<alpha>_mem \<Rightarrow> u" and
  \<gamma>2_mem :: "\<alpha>_mem \<Rightarrow> u"

nitpick_params [user_axioms, dont_box, show_all, atoms u = a b c d e f g h i j k l]


subsection {* Set Membership *}

axiomatization
  mem :: "u \<Rightarrow> u \<Rightarrow> bool" (infix "\<in>#" 50)
where
  mem_ext: "\<And>a b. \<gamma>2_mem a = \<gamma>2_mem b \<or>
    (\<exists>a' b'. \<gamma>1_mem a' = \<gamma>1_mem b' \<and> \<gamma>2_mem a' = \<gamma>2_mem a \<and> \<gamma>2_mem b' = \<gamma>2_mem b \<and>
       \<not> (\<gamma>1_mem a' \<in># \<gamma>2_mem a \<longleftrightarrow> \<gamma>1_mem a' \<in># \<gamma>2_mem b))" and
  mem_acyclic: "\<And>A. \<not> tranclp (\<lambda>x B. x \<in># B \<and> (\<exists>b. \<gamma>1_mem b = x \<and> \<gamma>2_mem b = B)) A A"






















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


subsection {* Empty Set *}



subsection {* Quantifiers *}

text \<open>
Nunchaku will look for finite models of @{type u}. Universal quantification
@{prop "\<forall>x :: u. P x"} in the original problem must be translated to
@{text "false asserting exists x : u. ~ P x"} to account for the incompleteness
of @{type u} w.r.t. the ZF universe it approximates, unless there is a guard
@{text "x \<in># \<dots>"} in @{prop "P x"}, in which case @{prop "\<forall>x :: u. P x"} can be
left alone.
\<close>

definition All_u :: "(u \<Rightarrow> bool) \<Rightarrow> bool" where
  "All_u P = (\<forall>x. P x \<and> Nitpick.unknown)"

(* use All_u? *)
lemma "\<forall>x. \<not> x \<in># emptyset"
  nitpick [satisfy, expect = genuine]
  nitpick [expect = none]
  sorry

lemma "\<exists>u. All_u (\<lambda>x. x \<in># u)"
  nitpick [satisfy, expect = none]
  nitpick [expect = genuine]
  sorry

lemma "(SOME x. \<not> x \<in># A) \<in># A"
  nitpick [expect = genuine]
  nitpick [satisfy, expect = none]
  oops

lemma "\<not> (SOME x. \<not> x \<in># A) \<in># A"
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
  app_ext: "\<And>f g. dom f = dom g \<and> (\<forall>x. x \<in># dom f \<longrightarrow> f \<cdot> x = g \<cdot> x) \<longrightarrow> f = g"

abbreviation mapsto :: "u \<Rightarrow> (u \<Rightarrow> u) \<Rightarrow> u" where
  "mapsto A f \<equiv> unique_unsafe (\<lambda>g. dom g = A \<and> (\<forall>x. x \<in># A \<longrightarrow> g \<cdot> x = f x))"

lemma "f = mapsto (dom f) (op \<cdot> f)"
  nitpick [expect = none]
  sorry


subsection {* Powerset *}

definition
  Pow :: "u \<Rightarrow> u"
where
  "Pow B = unique_unsafe (\<lambda>C. \<forall>A. A \<in># C \<longleftrightarrow> A \<subseteq># B)"

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
  "Union B = unique_unsafe (\<lambda>C. \<forall>x. x \<in># C \<longleftrightarrow> (\<exists>A. x \<in># A \<and> A \<in># B))"

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
