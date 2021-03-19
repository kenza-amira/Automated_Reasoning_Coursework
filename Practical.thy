theory Practical
imports Main
begin

section \<open>Part 1\<close>

(* 1 mark *)
lemma disjunction_idempotence:
  "A \<or> A \<longleftrightarrow> A"
  apply (rule iffI)
  apply (erule disjE)
  apply assumption+
  apply (rule disjI1)
  apply assumption
  done

(* 1 mark *)
lemma conjunction_idempotence:
  "A \<and> A \<longleftrightarrow> A"
  apply (rule iffI)
  apply (erule conjE)
  apply (assumption)
  apply (rule conjI)
  apply assumption+
  done

(* 1 mark *)
lemma disjunction_to_conditional:
  "(\<not> P \<or> R) \<longrightarrow> (P \<longrightarrow> R)"
  apply (rule impI)+
  apply (erule disjE)
  apply (erule notE)
  apply assumption +
  done


(* 1 mark *)
lemma
  "(\<exists>x. P x \<and> Q x) \<longrightarrow> (\<exists>x. P x) \<and> (\<exists>x. Q x)"
  apply (rule impI)
  apply (rule conjI)
  apply (erule exE, rule exI, erule conjE, assumption)+
  done
  

(* 1 mark *)
lemma
  "(\<not> (\<exists>x. \<not>P x) \<or> R) \<longrightarrow> ((\<exists>x. \<not> P x) \<longrightarrow> R)"
  apply (rule impI)
  apply (erule disjE)
   apply (rule impI)
  apply (erule notE)
  apply assumption
  apply (rule impI)
  apply assumption
  done


(* 2 marks *)
lemma
  "(\<forall>x. P x) \<longrightarrow> \<not> (\<exists>x. \<not> P x)" 
  apply (rule impI)
  apply (rule notI)
  apply (erule exE)
  apply (erule allE)
  apply (erule notE)
  apply assumption
  done

(* 3 marks *)
text \<open>Prove using ccontr\<close>
lemma em:
  "P \<or> \<not> P"
  apply (rule ccontr)
  apply (rule notE)
   apply assumption
  apply (rule disjI2)
  apply (rule notI)
  apply (erule notE)
  apply (rule disjI1)
  apply assumption
  done

(* 3 marks *)
text \<open>Prove using excluded middle\<close>
lemma notnotD:
  "\<not>\<not> P \<Longrightarrow> P"
  apply (cut_tac P ="P" in excluded_middle)
  apply (erule disjE)
  apply (erule notE)
  apply assumption +
  done

(* 3 marks *)
text \<open>Prove using double-negation (rule notnotD)\<close>
lemma classical:
  "(\<not> P \<Longrightarrow> P) \<Longrightarrow> P"
  apply (drule impI)
  apply (rule notnotD)
  apply (rule notI)
  apply (erule impE)
  apply assumption
  apply (erule notE)
  apply assumption
  done


(* 3 marks *)
text \<open>Prove using classical\<close>
lemma ccontr:
  "(\<not> P \<Longrightarrow> False) \<Longrightarrow> P"
  apply (drule impI)
  apply (rule classical)
  apply (erule impE)
  apply assumption
  apply (erule FalseE)
  done

(* 3 marks *)
lemma
  "(\<not> (\<forall>x. P x \<or> R x)) = (\<exists>x. \<not> P x \<and> \<not> R x)"
  apply (rule iffI)
   apply (rule classical)
   apply (erule notE)+
   apply (rule exI)
   apply (rule conjI)
    apply (rule notI)
  apply assumption
  apply (rule ccontr)
oops

(* 3 marks *)

lemma     
  "(\<exists>x. P x \<or> R x) = (\<not>((\<forall>x. \<not> P x) \<and> \<not> (\<exists>x. R x)))"
  apply (rule iffI)
  apply (rule notI)
  apply (erule exE)
  apply (erule conjE)
  apply (erule notE)+
  apply (rule exI)
  apply (erule disjE)
  apply (erule allE)
  apply (erule notE)
    apply assumption+
  apply (erule notE)
  apply (rule conjI)
   apply (rule allI)
   apply (rule notI)
  apply assumption


  oops
section \<open>Part 2.1\<close>

locale partof =
  fixes partof :: "'region \<Rightarrow> 'region \<Rightarrow> bool" (infix "\<sqsubseteq>" 100)
begin

(* 1 mark *)
definition properpartof :: "'region \<Rightarrow> 'region \<Rightarrow> bool" (infix "\<sqsubset>" 100) where
  "x \<sqsubset> y \<equiv> x \<sqsubseteq> y \<and> x \<noteq> y"

(* 1 mark *)
definition overlaps :: "'region \<Rightarrow> 'region \<Rightarrow> bool" (infix "\<frown>" 100) where
  "x \<frown> y \<equiv> (\<exists>z. z \<sqsubseteq> x  \<and> z \<sqsubseteq> y)"

definition disjoint :: "'region \<Rightarrow> 'region \<Rightarrow> bool" (infix "\<asymp>" 100) where
  "x \<asymp> y \<equiv> \<not> x \<frown> y"

(* 1 mark *)
definition partialoverlap :: "'region \<Rightarrow> 'region \<Rightarrow> bool" (infix "~\<frown>" 100) where
  "x ~\<frown> y \<equiv> x \<frown> y \<and> \<not>x \<sqsubseteq> y \<and>  \<not>y \<sqsubseteq> x "

(* 1 mark *)
definition sumregions :: "'region set \<Rightarrow> 'region \<Rightarrow> bool" ("\<Squnion> _ _" [100, 100] 100) where
  "\<Squnion> \<alpha> x \<equiv> (\<forall>y \<in> \<alpha>. y \<sqsubseteq> x) \<and> (\<forall>y. y \<sqsubseteq> x  \<longrightarrow> (\<exists>z \<in> \<alpha>. y \<frown> z))"

end

(* 1+1+1=3 marks *)
locale mereology = partof +
  assumes A1: "\<forall>xyz. x \<sqsubseteq> y \<and> y \<sqsubseteq> z  \<longrightarrow> x \<sqsubseteq> z "
      and A2: "\<forall> \<alpha>.  \<alpha> \<noteq> {}  \<longrightarrow> (\<exists>x. \<Squnion> \<alpha> x) "
      and A2': "\<forall>\<alpha>xy. \<Squnion> \<alpha> x \<and>  \<Squnion> \<alpha> y \<longrightarrow> x = y "
begin

section \<open>Part 2.2\<close>

(* 2 marks *)
theorem overlaps_sym:
  "(x \<frown> y) = (y \<frown> x)"
  apply (unfold overlaps_def)
  apply (rule iffI)
  apply (erule exE, erule conjE, rule exI, rule conjI, assumption+)+
  done

(* 1 mark *)
theorem in_sum_set_partof:
  "x \<in> \<alpha>  \<longrightarrow>  \<Squnion> \<alpha> x "
proof (unfold sumregions_def)
  show  "x \<in> \<alpha> \<longrightarrow> (\<forall>y\<in>\<alpha>. y \<sqsubseteq> x) \<and> (\<forall>y. y \<sqsubseteq> x \<longrightarrow>(\<exists>z\<in>\<alpha>. y \<frown> z))"
    using sumregions_def by blast
qed

(* 3 marks *)
theorem overlaps_refl:
  "x \<frown> x\<longrightarrow>  \<Squnion> \<alpha> x \<and> \<Squnion> \<alpha> y \<and> x = y"
proof (unfold overlaps_def)
  show "(\<exists>z. z \<sqsubseteq> x \<and> z \<sqsubseteq> x) \<longrightarrow> \<Squnion> \<alpha> x \<and> \<Squnion> \<alpha> y \<and> x = y"
    using sumregions_def A2' by blast
qed

(* 1 mark *)
theorem all_has_partof:
  "\<forall>r. \<exists>x. x \<sqsubset> r"
proof (unfold properpartof_def)
  show "\<forall>r. \<exists>x. x \<sqsubseteq> r \<and> x \<noteq> r"
    using properpartof_def by blast
qed

(* 2 marks *)
theorem partof_overlaps:
  assumes "x \<sqsubset> y"
  shows " \<forall>r. r \<sqsubset> x \<longrightarrow> r \<sqsubset> y"
proof (unfold properpartof_def)
  show " \<forall>r. r \<sqsubseteq> x \<and> r \<noteq> x \<longrightarrow> r \<sqsubseteq> y \<and> r \<noteq> y"
  using A1 properpartof_def by blast
qed

(* 1 mark *)
theorem sum_parts_eq:
  "\<Squnion> {x} x"
proof (unfold sumregions_def)
  show "(\<forall>y\<in>{x}. y \<sqsubseteq> x) \<and> (\<forall>y. y \<sqsubseteq> x \<longrightarrow>(\<exists>z\<in>{x}. y \<frown> z))"
    by blast
qed

(* 2 marks *)
theorem sum_relation_is_same':
  assumes "\<And>c. r y c \<Longrightarrow> c \<sqsubseteq> y"
      and "\<And>f. y \<frown> f \<Longrightarrow> \<exists>g. r y g \<and> g \<frown> f"
      and "\<Squnion> {y} x"
    shows "\<Squnion> {k. r y k} x"
proof (unfold sumregions_def)
  show "(\<forall>y\<in>Collect (r y).y \<sqsubseteq> x) \<and> (\<forall>ya. ya \<sqsubseteq> x \<longrightarrow> (\<exists>z\<in>Collect (r y). ya \<frown> z))"
    using sumregions_def by blast
qed


(* 1 mark *)
theorem overlap_has_partof_overlap:
  assumes "undefined"
  shows "undefined"
oops

(* 1 marks *)
theorem sum_parts_of_one_eq:
  assumes "undefined"
  shows "undefined"
oops

(* 5 marks *)
theorem both_partof_eq:
  assumes "undefined"
  shows "undefined"
oops

(* 4 marks *)
theorem sum_all_with_parts_overlapping:
  assumes "undefined"
  shows "undefined"
oops

(* 2 marks *)
theorem sum_one_is_self:
  "undefined"
oops

(* 2 marks *)
theorem sum_all_with_parts_overlapping_self:
  "undefined"
oops

(* 4 marks *)
theorem proper_have_nonoverlapping_proper:
  assumes "undefined"
  shows "undefined"
oops

(* 1 mark *)
sublocale parthood_partial_order: order "(\<sqsubseteq>)" "(\<sqsubset>)"
proof
  show "\<And>x y. x \<sqsubset> y = (x \<sqsubseteq> y \<and> \<not> y \<sqsubseteq> x)"
    sorry
next
  show "\<And>x. x \<sqsubseteq> x"
    sorry
next
  show "\<And>x y z. \<lbrakk>x \<sqsubseteq> y; y \<sqsubseteq> z\<rbrakk> \<Longrightarrow> x \<sqsubseteq> z"
    sorry
next
  show "\<And>x y. \<lbrakk>x \<sqsubseteq> y; y \<sqsubseteq> x\<rbrakk> \<Longrightarrow> x = y"
    sorry
qed

end

section \<open>Part 2.3\<close>

locale sphere =
  fixes sphere :: "'a \<Rightarrow> bool"
begin

abbreviation AllSpheres :: "('a \<Rightarrow> bool) \<Rightarrow> bool" (binder "\<forall>\<degree>" 10) where
  "\<forall>\<degree>x. P x \<equiv> \<forall>x. sphere x \<longrightarrow> P x"

abbreviation ExSpheres :: "('a \<Rightarrow> bool) \<Rightarrow> bool" (binder "\<exists>\<degree>" 10) where
  "\<exists>\<degree>x. P x \<equiv> \<exists>x. sphere x \<and> P x"

end

locale mereology_sphere = mereology partof + sphere sphere
  for partof :: "'region \<Rightarrow> 'region \<Rightarrow> bool" (infix "\<sqsubseteq>" 100)
  and sphere :: "'region \<Rightarrow> bool"
begin

definition exttan :: "'region \<Rightarrow> 'region \<Rightarrow> bool" where
  "exttan a b \<equiv> sphere a \<and> sphere b \<and> a \<asymp> b \<and> (\<forall>\<degree>x y. a \<sqsubseteq> x \<and> a \<sqsubseteq> y \<and> b \<asymp> x \<and> b \<asymp> y
                                                        \<longrightarrow> x \<sqsubseteq> y \<or> y \<sqsubseteq> x)"

definition inttan :: "'region \<Rightarrow> 'region \<Rightarrow> bool" where
  "inttan a b \<equiv> sphere a \<and> sphere b \<and> a \<asymp> b \<and> (\<forall>\<degree>x y. a \<sqsubseteq> x \<and> a \<sqsubseteq> y \<and> x \<sqsubseteq> b \<and> y \<sqsubseteq> b
                                                        \<longrightarrow> x \<sqsubseteq> y \<or> y \<sqsubseteq> x)"

definition extdiam :: "'region \<Rightarrow> 'region \<Rightarrow> 'region \<Rightarrow> bool" where
  "extdiam a b c \<equiv> exttan a c \<and> exttan b c
                 \<and> (\<forall>\<degree>x y. x \<asymp> c \<and> y \<asymp> c \<and> a \<sqsubseteq> x \<and> b \<sqsubseteq> y \<longrightarrow> x \<asymp> y)"

definition intdiam :: "'region \<Rightarrow> 'region \<Rightarrow> 'region \<Rightarrow> bool" where
  "intdiam a b c \<equiv> inttan a c \<and> inttan b c
                 \<and> (\<forall>\<degree>x y. x \<asymp> c \<and> y \<asymp> c \<and> exttan a x \<and> exttan b y \<longrightarrow> x \<asymp> y)"

abbreviation properconcentric :: "'region \<Rightarrow> 'region \<Rightarrow> bool" where
  "properconcentric a b \<equiv> a \<sqsubset> b
                        \<and> (\<forall>\<degree>x y. extdiam x y a \<and> inttan x b \<and> inttan y b \<longrightarrow> intdiam x y b)"

definition concentric :: "'region \<Rightarrow> 'region \<Rightarrow> bool" (infix "\<odot>" 100) where
  "a \<odot> b \<equiv> sphere a \<and> sphere b \<and> (a = b \<or> properconcentric a b \<or> properconcentric b a)"

definition onboundary :: "'region \<Rightarrow> 'region \<Rightarrow> bool" where
  "onboundary s r \<equiv> sphere s \<and> (\<forall>s'. s' \<odot> s \<longrightarrow> s' \<frown> r \<and> \<not> s' \<sqsubseteq> r)"

definition equidistant3 :: "'region \<Rightarrow> 'region \<Rightarrow> 'region \<Rightarrow> bool" where
  "equidistant3 x y z \<equiv> \<exists>\<degree>z'. z' \<odot> z \<and> onboundary y z' \<and> onboundary x z'"

definition betw :: "'region \<Rightarrow> 'region \<Rightarrow> 'region \<Rightarrow> bool" ("[_ _ _]" [100, 100, 100] 100) where
  "[x y z] \<equiv> sphere x \<and> sphere z
             \<and> (x \<odot> y \<or> y \<odot> z
                \<or> (\<exists>x' y' z' v w. x' \<odot> x \<and> y' \<odot> y \<and> z' \<odot> z
                                  \<and> extdiam x' y' v \<and> extdiam v w y' \<and> extdiam y' z' w))"

definition mid :: "'region \<Rightarrow> 'region \<Rightarrow> 'region \<Rightarrow> bool" where
  "mid x y z \<equiv> [x y z] \<and> (\<exists>\<degree>y'. y' \<odot> y \<and> onboundary x y' \<and> onboundary z y')"

definition equidistant4 :: "'region \<Rightarrow> 'region \<Rightarrow> 'region \<Rightarrow> 'region \<Rightarrow> bool" ("_ _ \<doteq> _ _" [100, 100, 100, 100] 100) where
  "x y \<doteq> z w \<equiv> \<exists>\<degree>u v. mid w u y \<and> mid x u v \<and> equidistant3 v z y"

definition oninterior :: "'region \<Rightarrow> 'region \<Rightarrow> bool" where
  "oninterior s r \<equiv> \<exists>s'. s' \<odot> s \<and> s' \<sqsubseteq> r"

definition nearer :: "'region \<Rightarrow> 'region \<Rightarrow> 'region \<Rightarrow> 'region \<Rightarrow> bool" where
  "nearer w x y z \<equiv> \<exists>\<degree>x'. [w x x'] \<and> \<not> x \<odot> x' \<and> w x' \<doteq> y z"

end

locale partial_region_geometry = mereology_sphere partof sphere
  for partof :: "'region \<Rightarrow> 'region \<Rightarrow> bool" (infix "\<sqsubseteq>" 100)
  and sphere :: "'region \<Rightarrow> bool" +
  assumes A4: "\<lbrakk>x \<odot> y; y \<odot> z\<rbrakk> \<Longrightarrow> x \<odot> z"
      and A5: "\<lbrakk>x y \<doteq> z w; x' \<odot> x\<rbrakk> \<Longrightarrow> x' y \<doteq> z w"
      and A6: "\<lbrakk>sphere x; sphere y; \<not> x \<odot> y\<rbrakk>
               \<Longrightarrow> \<exists>\<degree>s. \<forall>\<degree>z. oninterior z s = nearer x z x y"
      and A7: "sphere x \<Longrightarrow> \<exists>\<degree>y. \<not> x \<odot> y \<and> (\<forall>\<degree>z. oninterior z x = nearer x z x y)"
      and A8: "x \<sqsubseteq> y = (\<forall>s. oninterior s x \<longrightarrow> oninterior s y)"
      and A9: "\<exists>\<degree>s. s \<sqsubseteq> r"
begin

(* 2 marks *)
thm equiv_def
theorem conc_equiv:
  "equiv undefined undefined"
oops

(* 6 marks *)
theorem region_is_spherical_sum:
  "undefined"
oops

(* 1 mark *)
theorem region_spherical_interior:
  "undefined"
oops

(* 2 marks *)
theorem equal_interiors_equal_regions:
  assumes "undefined"
  shows "undefined"
oops

(* 2 marks *)
theorem proper_have_nonoverlapping_proper_sphere:
  assumes "undefined"
  shows "undefined"
oops

(* 4 marks *)
theorem not_sphere_spherical_parts_gt1:
  assumes "undefined"
      and "undefined"
  shows "undefined"
oops

end

section \<open>Part 3\<close>

context mereology_sphere
begin

(* 3 marks *)
lemma
  assumes T4: "\<And>x y. \<lbrakk>sphere x; sphere y\<rbrakk> \<Longrightarrow> x y \<doteq> y x"
      and A9: "\<exists>\<degree>s. s \<sqsubseteq> r"
  shows False
oops

(* 3 marks *)
definition equidistant3' :: "'region \<Rightarrow> 'region \<Rightarrow> 'region \<Rightarrow> bool" where
  "equidistant3' x y z \<equiv> undefined"

no_notation equidistant4 ("_ _ \<doteq> _ _" [100, 100, 100, 100] 100)

definition equidistant4' :: "'region \<Rightarrow> 'region \<Rightarrow> 'region \<Rightarrow> 'region \<Rightarrow> bool" ("_ _ \<doteq> _ _" [100, 100, 100, 100] 100) where
  "x y \<doteq> z w \<equiv> \<exists>\<degree>u v. mid w u y \<and> mid x u v \<and> equidistant3' v z y"

end

datatype two_reg = Left | Right | Both

(* 2 marks *)
definition tworeg_partof :: "two_reg \<Rightarrow> two_reg \<Rightarrow> bool" (infix "\<sqsubseteq>" 100) where
  "x \<sqsubseteq> y \<equiv> undefined"

(* 12 marks *)
interpretation mereology "(\<sqsubseteq>)"
oops


end