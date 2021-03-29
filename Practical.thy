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
lemma excluded_middle:
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
  apply (cut_tac P ="P" in HOL.excluded_middle)
  apply (erule disjE)
  apply (erule notE)
  apply assumption +
  done

(* 3 marks *)
text \<open>Prove using double-negation (rule notnotD)\<close>
lemma classical:
  "(\<not> P \<Longrightarrow> P) \<Longrightarrow> P"
  apply (rule notnotD)
  apply (drule impI)
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
  apply (rule classical)
  apply (drule impI)
  apply (erule impE)
  apply assumption
  apply (rule_tac P = "\<not>P" in notE)
  apply (rule notI)
  apply assumption +
  done

(* 3 marks *)
lemma
  "(\<not> (\<forall>x. P x \<or> R x)) = (\<exists>x. \<not> P x \<and> \<not> R x)"
  apply (rule iffI)
   apply (rule exI)
   apply (rule notE)
    apply assumption
   apply (rule allI)
   apply (rule notE)
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
  "x \<asymp> y \<equiv> \<not> (x \<frown> y)"

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
  "x \<in> \<alpha> \<and> \<Squnion> \<alpha> y  \<longrightarrow>  x \<sqsubseteq> y "
proof -
  show  "x \<in> \<alpha> \<and> \<Squnion> \<alpha> y  \<longrightarrow>  x \<sqsubseteq> y "
    using sumregions_def by simp
qed

(* 3 marks *)
theorem overlaps_refl:
  "a \<frown> a"
proof -
  have "{a} \<noteq> {}" by simp
  then  have "(\<exists>x. \<Squnion> {a} x)" using A2 by simp
  then obtain x where "\<Squnion> {a} x" by blast
  then have s: "(\<forall>y \<in> {a}. y \<sqsubseteq> x) \<and> (\<forall>y. y \<sqsubseteq> x  \<longrightarrow> (\<exists>z \<in> {a}. y \<frown> z))"
    using sumregions_def by simp
  then have "a \<sqsubseteq> x" by simp
  then show  "a \<frown> a" using s by simp
qed

(* 1 mark *)
theorem all_has_partof:
   "\<forall>r. \<exists>x. x \<sqsubseteq> r"
proof
  fix r
  have "r \<frown> r" using overlaps_refl by blast
  then have "\<exists>z. z \<sqsubseteq> r  \<and> z \<sqsubseteq> r" using overlaps_def by blast
  then obtain z where "z \<sqsubseteq> r  \<and> z \<sqsubseteq> r" by blast
  then have "z \<sqsubseteq> r" by simp
  then show "\<exists>x. x \<sqsubseteq> r"  by blast
qed

(* 2 marks *)
(*theorem partof_overlaps:
  assumes a:"r \<sqsubseteq> x"
    and b:"x \<sqsubseteq> y"
  shows "\<exists>s. s \<sqsubseteq> x \<and> s \<frown> y"
proof -
  have "r \<sqsubseteq> y" using a b A1 by blast
  then show "\<exists>s. s \<sqsubseteq> x \<and> s \<frown> y" 
    using A1 all_has_partof local.a overlaps_def by blast
qed*)

theorem partof_overlaps:
  assumes "x \<sqsubseteq> y"
  shows "r \<sqsubseteq> x \<Longrightarrow> r \<frown> y"
proof -
  assume "r \<sqsubseteq> x"
  then have "r \<sqsubseteq> y" using assms A1 by blast
  then show " r \<frown> y" 
    using A1 all_has_partof assms overlaps_def by blast
qed

(* 1 mark *)
theorem sum_parts_eq:
"\<Squnion> {r. r \<sqsubseteq> x } x"
proof (unfold sumregions_def)
  show "(\<forall>y\<in>{r. r \<sqsubseteq> x}. y \<sqsubseteq> x) \<and>(\<forall>y. y \<sqsubseteq> x \<longrightarrow> (\<exists>z \<in>{r. r \<sqsubseteq> x}. y \<frown> z))"
  using overlaps_refl by auto
qed

(* 2 marks *)
theorem sum_relation_is_same':
 assumes a: "\<And>c. r y c \<Longrightarrow> c \<sqsubseteq> y"
      and b: "\<And>f. y \<frown> f \<Longrightarrow> \<exists>g. r y g \<and> g \<frown> f"
      and c: "\<Squnion> {y} x"
  shows "\<Squnion> {k. r y k} x"
proof (unfold sumregions_def, safe)
  fix ya
  have  "y \<sqsubseteq> x" 
    using c sumregions_def by blast
  then show  "r y ya \<Longrightarrow> ya \<sqsubseteq> x"
    using a c A1 by blast
  then show "\<And>ya. ya \<sqsubseteq> x \<Longrightarrow>\<exists>z\<in>Collect (r y). ya \<frown> z"
    using b c overlaps_sym sumregions_def by auto
qed


(* 1 mark *)
theorem overlap_has_partof_overlap:
  assumes a: "e \<frown> f"
  shows "\<exists>r. r \<sqsubseteq> e \<and> r \<frown> f"
proof -
  have "\<exists>z. z \<sqsubseteq> e \<and> z \<sqsubseteq> f" using a overlaps_def by blast
  then obtain z where "z \<sqsubseteq> e \<and> z \<sqsubseteq> f" by blast
  then show "\<exists>r. r \<sqsubseteq> e \<and> r \<frown> f"
    using A1 overlaps_def overlaps_refl by blast
qed

(* 1 marks *)
theorem sum_parts_of_one_eq:
  assumes "\<Squnion> {x} y"
  shows "\<Squnion> {w. w \<sqsubseteq> x} y"
proof -
  from sum_relation_is_same' [where r = "(\<lambda> x w. w \<sqsubseteq> x)"]
  show "\<Squnion> {w. w \<sqsubseteq> x} y"
    using assms overlap_has_partof_overlap by auto
qed
(* 5 marks *)
theorem both_partof_eq:
  assumes a:"x \<sqsubseteq> y"
    and b: "y \<sqsubseteq> x"
and c: "\<Squnion> {w. w \<sqsubseteq> x} x"
  shows "\<Squnion> {r. r \<sqsubseteq> x} y"
proof (rule ccontr)
  assume "\<not> \<Squnion> {r. r \<sqsubseteq> x} y "
  then have "\<exists>z. (z \<sqsubseteq> x \<and> \<not>(z \<sqsubseteq> y)) \<or> (z \<sqsubseteq> y \<and> (\<forall>s. s \<sqsubseteq> x \<longrightarrow> \<not> (s \<frown> z)))"
    using sumregions_def assms partof_overlaps by blast
  then obtain z where "(z \<sqsubseteq> x \<and> \<not>(z \<sqsubseteq> y)) \<or> (z \<sqsubseteq> y \<and> (\<forall>s. s \<sqsubseteq> x \<longrightarrow> \<not> (s \<frown> z)))" by blast
  from this show False
  proof
    assume z: "(z \<sqsubseteq> x \<and> \<not>(z \<sqsubseteq> y))"
    show False
      using A1 z a by blast
  next
    assume w: "z \<sqsubseteq> y \<and> (\<forall>s. s \<sqsubseteq> x \<longrightarrow> \<not> s \<frown> z)"
    show False
      using A1 w a b overlaps_sym partof_overlaps by blast
  qed 
qed

(* 4 marks *)
theorem sum_all_with_parts_overlapping:
  assumes "\<Squnion> {z. \<forall>r. r \<sqsubseteq> z \<longrightarrow> r \<frown> y} x"
  shows "\<Squnion> {y} x"
proof (rule ccontr)
  assume "\<not> \<Squnion> {y} x"
  then have "\<not>(y \<sqsubseteq> x) \<or> (\<exists>w. w \<sqsubseteq> x \<and> \<not>(w \<frown> y))"
    using sumregions_def by auto
  from this show False
  proof
    assume "\<not>(y \<sqsubseteq> x)"
    have "\<forall>r. r \<sqsubseteq> y \<longrightarrow> r \<frown> y"
      using A1 all_has_partof overlaps_def by blast
    then have " y \<in> {z. \<forall>r. r \<sqsubseteq> z \<longrightarrow> r \<frown> y}"
      by simp
    then have "y \<sqsubseteq> x" using assms sumregions_def by auto
    show False
      using \<open>\<not> y \<sqsubseteq> x\<close> \<open>y \<sqsubseteq> x\<close> by auto
  next
    assume "(\<exists>w. w \<sqsubseteq> x \<and> \<not>(w \<frown> y))"
    then obtain w where " w \<sqsubseteq> x \<and> \<not>(w \<frown> y)" by blast
    have " (\<forall>ya. ya \<sqsubseteq> x \<longrightarrow> (\<exists>z\<in>{z. \<forall>r. r \<sqsubseteq> z \<longrightarrow> r \<frown> y}.  ya \<frown> z))" 
      using assms sumregions_def by blast
    then have "(\<exists>z. z\<in>{z. \<forall>r. r \<sqsubseteq> z \<longrightarrow> r \<frown> y } \<and>  w \<frown> z \<and> (\<forall>t. t \<sqsubseteq> z \<longrightarrow> t \<frown> y))"
      using \<open>w \<sqsubseteq> x \<and> \<not> w \<frown> y\<close> by blast
    then obtain z where "z\<in>{z. \<forall>r. r \<sqsubseteq> z \<longrightarrow> r \<frown> y} \<and>  w \<frown> z" and "\<forall>t. t \<sqsubseteq> z \<longrightarrow> t \<frown> y" by auto
    then have "\<exists>wz. wz \<sqsubseteq> w \<and> wz \<sqsubseteq> z" using overlaps_def by blast
    then obtain wz where "wz \<sqsubseteq> w \<and> wz \<sqsubseteq> z" by blast
    then have "wz \<frown> y"
      using \<open>\<forall>t. t \<sqsubseteq> z \<longrightarrow> t \<frown> y\<close> by simp
    then have "\<exists>wzy. wzy \<sqsubseteq> wz \<and> wzy \<sqsubseteq> y" using overlaps_def by blast
    then have "wzy \<sqsubseteq> w" 
      using A1 \<open>w \<sqsubseteq> x \<and> \<not> w \<frown> y\<close> \<open>wz \<sqsubseteq> w \<and> wz \<sqsubseteq> z\<close> overlaps_def by blast
    show False
      using A1 \<open>w \<sqsubseteq> x \<and> \<not> w \<frown> y\<close> \<open>wz \<frown> y\<close> \<open>wz \<sqsubseteq> w \<and> wz \<sqsubseteq> z\<close> overlaps_def by blast
  qed
qed
(* 2 marks *)
theorem sum_one_is_self:
 "\<Squnion> {x} x"
proof -  
  have "{x} \<noteq> {}" by simp
  then have "\<exists>y. \<Squnion> {x} y" using A2 by simp
  then obtain y where "\<Squnion> {x} y" by blast
  have "\<Squnion> {r. r \<sqsubseteq> x} x" using sum_parts_eq by blast
  then show "\<Squnion> {x} x" 
    using A2' \<open>\<Squnion> {x} y\<close> sum_parts_of_one_eq by blast
qed

(* 2 marks *)
theorem sum_all_with_parts_overlapping_self:
  "\<Squnion> {z. \<forall>r. r \<sqsubseteq> z \<longrightarrow> r \<frown> x} x"
  sorry
(*proof -
  have one: "\<forall>r. r \<sqsubseteq> x \<longrightarrow> r \<frown> x"
    using A1 overlaps_def overlaps_refl by blast
  have two:  "\<Squnion> {x} x" using sum_one_is_self by blast
  have "x \<in> {z. \<forall>r. r \<sqsubseteq> z \<longrightarrow> r \<frown> x}" using one by simp
  then show "\<Squnion> {z. \<forall>r. r \<sqsubseteq> z \<longrightarrow> r \<frown> x} x" using two

  sorry*)


(* 4 marks *)
theorem proper_have_nonoverlapping_proper:
  assumes a: "s \<sqsubset> r"
  shows "\<exists>g. g \<sqsubset> r \<and> (g \<asymp> s)"
  sorry
(*proof (unfold disjoint_def, unfold properpartof_def)
  have "s \<sqsubseteq> r \<and> s \<noteq> r" using assms properpartof_def by blast
  then have "\<exists>g. g \<sqsubseteq> r \<and> g \<noteq> s"
    using sum_one_is_self sumregions_def by auto
  then obtain g where "g \<sqsubseteq> r \<and> g \<noteq> s" by auto
  then have "g \<asymp> s" using disjoint_def*)

(* 1 mark *)
sublocale parthood_partial_order: order "(\<sqsubseteq>)" "(\<sqsubset>)"
proof
  show "\<And>x y. x \<sqsubset> y = (x \<sqsubseteq> y \<and> \<not> y \<sqsubseteq> x)"
    using A2' both_partof_eq properpartof_def sum_parts_eq by blast
next
  show "\<And>x. x \<sqsubseteq> x"
    using in_sum_set_partof sum_one_is_self by auto
next
  show "\<And>x y z. \<lbrakk>x \<sqsubseteq> y; y \<sqsubseteq> z\<rbrakk> \<Longrightarrow> x \<sqsubseteq> z"
    using A1 by blast
next
  show "\<And>x y. \<lbrakk>x \<sqsubseteq> y; y \<sqsubseteq> x\<rbrakk> \<Longrightarrow> x = y"
    using A2' both_partof_eq sum_parts_eq by blast
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
thm equiv_type
theorem conc_equiv:
  "equiv undefined undefined"
  oops

lemma conc_refl: "concentric a a"
  sorry
lemma conc_sym: "concentric a b = concentric b a"
  sorry

(* 6 marks *)
theorem region_is_spherical_sum:
  "\<Squnion> {s. (s\<sqsubseteq>r \<and> sphere s)} r"
proof (rule ccontr)
  assume " \<not> \<Squnion> {s. s \<sqsubseteq> r \<and> sphere s} r"
  then have " \<not>(\<forall>y \<in>{s. s \<sqsubseteq> r \<and>  sphere s}.  y \<sqsubseteq> r) \<or> \<not>(\<forall>y. y \<sqsubseteq> r \<longrightarrow> (\<exists>z\<in>{s. s \<sqsubseteq> r \<and> sphere s}. y \<frown> z))"
    using sumregions_def by blast
  from this show False
  proof 
    assume " \<not> (\<forall>y\<in>{s. s \<sqsubseteq> r \<and> sphere s}. y \<sqsubseteq> r)"
    show False
      sorry
  next 
    assume "\<not>(\<forall>y. y \<sqsubseteq> r \<longrightarrow> (\<exists>z\<in>{s. s \<sqsubseteq> r \<and> sphere s}. y \<frown> z))"
    show False
      sorry
  qed
qed


(* 1 mark *)
theorem region_spherical_interior:
  "oninterior s r \<longleftrightarrow> (\<exists>s'. s' \<sqsubseteq> r \<and> oninterior s s')"
proof (rule iffI, unfold oninterior_def)
  assume "\<exists>s'. s' \<odot> s \<and>  s' \<sqsubseteq> r"
  then show " \<exists>s'. s' \<sqsubseteq> r \<and> (\<exists>s'a. s'a \<odot> s \<and>  s'a \<sqsubseteq> s')" 
    by blast
next
  assume "\<exists>s'. s' \<sqsubseteq> r \<and> (\<exists>s'a.   s'a \<odot> s \<and>  s'a \<sqsubseteq> s')"
  then show "\<exists>s'. s' \<odot> s \<and> s' \<sqsubseteq> r"
    using A1 by blast
qed

thm parthood_partial_order.antisym
(* 2 marks *)
(*Axiom 8 allows us to show partial parthood, we can also derive the LHS
from the RHS because of the double sided arrow which happen to be our assumptions*)
theorem equal_interiors_equal_regions:
  assumes a: "\<forall>s. oninterior s x = oninterior s y"
  shows "y = x"
proof -
  have b: "\<forall>s. oninterior s x \<longrightarrow>oninterior s y" using a by simp
  fix s
  have c: "\<forall>s. oninterior s y \<longrightarrow>oninterior s x" using a by simp
  fix s
  have d: "y \<sqsubseteq> x" using A8 c by blast
  have "x \<sqsubseteq> y" using A8 b by blast
  then show "y=x" using parthood_partial_order.antisym using d by blast
qed 

(* 2 marks *)
theorem proper_have_nonoverlapping_proper_sphere:
  assumes "s \<sqsubset> r"
  shows" \<exists>\<degree>p. p \<sqsubset> r \<and> \<not> p \<frown> s"
proof -
  show " \<exists>\<degree>p. p \<sqsubset> r \<and> \<not> p \<frown> s"
    using assms conc_refl concentric_def disjoint_def 
      proper_have_nonoverlapping_proper
    by auto
qed

(* 4 marks *)
theorem not_sphere_spherical_parts_gt1:
  assumes "\<not> sphere(s)"
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

(* I have added a condition i.e "sphere z" because after looking at the definitions provided 
I could tell that y is already considered a sphere in the onboundary definition,
z' is also considered to be a sphere thanks to the existential quantifier leaving us with z 
that is only considered to be a region.*)
definition equidistant3' :: "'region \<Rightarrow> 'region \<Rightarrow> 'region \<Rightarrow> bool" where
"equidistant3' x y z \<equiv> \<exists>\<degree>z'. z' \<odot> z \<and> onboundary y z' \<and> onboundary x z' \<and> sphere z"

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