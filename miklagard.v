(******************************************************************************)
(*                                                                            *)
(*           Miklagard: Rus'-Byzantine Treaty and Varangian Service           *)
(*                                                                            *)
(*     Rus'-Byzantine treaty provisions (907, 911, 944/945, 971) from the     *)
(*     Primary Chronicle: merchant admissibility, charter and arms            *)
(*     requirements, silk and sojourn limits, provision-derived treaty        *)
(*     favorability, criminal reciprocity, captives and ransom, maritime      *)
(*     salvage, Chersonesos protection, Varangian Guard eras and              *)
(*     composition, polutasvarf, envoy onomastics, and route order theory.    *)
(*                                                                            *)
(*     "And Oleg hung his shield upon the gate, to show his victory."         *)
(*     - Primary Chronicle, sub anno 907                                      *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: February 20, 2026                                                *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Arith List Bool Lia.
Import ListNotations.

(* ================================================================== *)
(*  SECTION 1: TEMPORAL AND POLITICAL FRAMEWORK                        *)
(* ================================================================== *)

(** A year in the Anno Mundi calendar used by the Primary Chronicle,
    or converted to CE. We use CE throughout. *)
Definition year := nat.

Inductive Civilization :=
  | Norse        (* Scandinavian homelands *)
  | Rus          (* Kievan Rus' - Norse-Slavic polity *)
  | Byzantine    (* Eastern Roman Empire *)
  | AngloSaxon   (* Pre-Conquest England *)
  | Norman.      (* Post-1066 *)

Inductive Religion :=
  | ChristianOrthodox
  | NorsePagan      (* Perun/Thor oath tradition *)
  | ChristianLatin.

(** The four major Rus'-Byzantine treaties preserved in the PVL. *)
Inductive Treaty :=
  | Treaty_907   (* Oleg's preliminary raid settlement *)
  | Treaty_911   (* Oleg's comprehensive trade/criminal law *)
  | Treaty_944   (* Igor's post-war settlement, less favorable *)
  | Treaty_971.  (* Sviatoslav's capitulation at Dorostolon *)

Definition treaty_year (t : Treaty) : year :=
  match t with
  | Treaty_907 => 907
  | Treaty_911 => 911
  | Treaty_944 => 944
  | Treaty_971 => 971
  end.

Theorem treaty_year_injective :
  forall t1 t2, treaty_year t1 = treaty_year t2 -> t1 = t2.
Proof.
  intros t1 t2 H; destruct t1, t2; simpl in H; try reflexivity; lia.
Qed.

(** Source status. The 911, 944 and 971 texts are diplomatic documents
    copied into the chronicle; the 907 agreement survives only as the
    chronicler's narrative, and its independent existence is disputed
    (Shakhmatov's extraction thesis). *)
Inductive TreatySource :=
  | DiplomaticText
  | ChronicleOnly.

Definition treaty_source (t : Treaty) : TreatySource :=
  match t with
  | Treaty_907 => ChronicleOnly
  | _          => DiplomaticText
  end.

Theorem diplomatic_texts_enumerated :
  forall t, treaty_source t = DiplomaticText ->
    t = Treaty_911 \/ t = Treaty_944 \/ t = Treaty_971.
Proof.
  intros t H; destruct t.
  - discriminate.
  - left; reflexivity.
  - right; left; reflexivity.
  - right; right; reflexivity.
Qed.

(* ================================================================== *)
(*  SECTION 2: TRADE ROUTE - THE ROAD TO THE GREEKS                    *)
(*  (Old Norse: Austrvegr; Slavic: put' iz variag v greki)             *)
(* ================================================================== *)

Inductive Waypoint :=
  | Birka           (* Swedish emporium, active to c. 975 *)
  | Sigtuna         (* Swedish royal seat, founded c. 980 *)
  | Aldeigja        (* Staraya Ladoga - first Rus' settlement *)
  | Holmgardr       (* Novgorod - Rurik's seat from 862 *)
  | Koenugard       (* Kiev - capital from 882 *)
  | Beloberezhye    (* Dnieper mouth - jointly administered *)
  | BlackSea_Open   (* Open water crossing *)
  | Miklagard.      (* Constantinople *)

(** Waypoints are ordered along the route. *)
Definition waypoint_order (w : Waypoint) : nat :=
  match w with
  | Birka         => 0
  | Sigtuna       => 1
  | Aldeigja       => 2
  | Holmgardr      => 3
  | Koenugard      => 4
  | Beloberezhye   => 5
  | BlackSea_Open  => 6
  | Miklagard      => 7
  end.

Definition on_route (w1 w2 : Waypoint) : bool :=
  waypoint_order w1 <? waypoint_order w2.

(** The route as explicit data, agreeing with the numeric order. *)
Definition route_list : list Waypoint :=
  [Birka; Sigtuna; Aldeigja; Holmgardr; Koenugard;
   Beloberezhye; BlackSea_Open; Miklagard].

Theorem route_list_indexes :
  forall w, nth_error route_list (waypoint_order w) = Some w.
Proof. destruct w; reflexivity. Qed.

Theorem route_list_complete :
  forall w, In w route_list.
Proof.
  destruct w; simpl; repeat (first [left; reflexivity | right]).
Qed.

Theorem route_list_nodup : NoDup route_list.
Proof. repeat constructor; simpl; intuition discriminate. Qed.

Theorem route_list_length : length route_list = 8.
Proof. reflexivity. Qed.

(** on_route is a strict total order. *)
Theorem waypoint_order_injective :
  forall w1 w2, waypoint_order w1 = waypoint_order w2 -> w1 = w2.
Proof.
  intros w1 w2 H; destruct w1, w2; simpl in H; try reflexivity; lia.
Qed.

Theorem route_irreflexive :
  forall w, on_route w w = false.
Proof. intros w; unfold on_route; apply Nat.ltb_irrefl. Qed.

Theorem route_transitive :
  forall w1 w2 w3,
    on_route w1 w2 = true -> on_route w2 w3 = true -> on_route w1 w3 = true.
Proof.
  intros w1 w2 w3 H1 H2; unfold on_route in *.
  apply Nat.ltb_lt in H1. apply Nat.ltb_lt in H2.
  apply Nat.ltb_lt. lia.
Qed.

Theorem route_asymmetric :
  forall w1 w2, on_route w1 w2 = true -> on_route w2 w1 = false.
Proof.
  intros w1 w2 H; unfold on_route in *.
  apply Nat.ltb_lt in H. apply Nat.ltb_ge. lia.
Qed.

Theorem route_trichotomy :
  forall w1 w2, on_route w1 w2 = true \/ on_route w2 w1 = true \/ w1 = w2.
Proof.
  intros w1 w2.
  destruct (Nat.lt_trichotomy (waypoint_order w1) (waypoint_order w2))
    as [Hlt | [Heq | Hgt]].
  - left. unfold on_route. apply Nat.ltb_lt. exact Hlt.
  - right; right. apply waypoint_order_injective. exact Heq.
  - right; left. unfold on_route. apply Nat.ltb_lt. exact Hgt.
Qed.

Theorem route_monotone :
  forall w1 w2,
    on_route w1 w2 = true ->
    waypoint_order w1 < waypoint_order w2.
Proof.
  intros w1 w2 H.
  unfold on_route in H.
  apply Nat.ltb_lt in H. exact H.
Qed.

(** Birka is initial and Miklagard is terminal. *)
Theorem birka_initial :
  forall w, on_route w Birka = false.
Proof. destruct w; reflexivity. Qed.

Theorem miklagard_terminal :
  forall w, w <> Miklagard -> on_route w Miklagard = true.
Proof.
  intros w Hneq.
  unfold on_route.
  apply Nat.ltb_lt.
  destruct w; simpl; try lia.
  contradiction.
Qed.

Theorem nothing_beyond_miklagard :
  forall w, on_route Miklagard w = false.
Proof.
  intros w. unfold on_route. simpl.
  destruct w; reflexivity.
Qed.

(** Birka and Sigtuna are successive in time, not both transited on
    one voyage: Birka's activity ceases c. 975 and Sigtuna is founded
    c. 980. The route order coexists with temporal succession. *)
Definition birka_decline : year := 975.
Definition sigtuna_founded : year := 980.

Definition birka_active (y : year) : bool := y <? birka_decline.
Definition sigtuna_active (y : year) : bool := sigtuna_founded <=? y.

Theorem emporia_succession :
  forall y, birka_active y = true -> sigtuna_active y = false.
Proof.
  intros y H. unfold birka_active, birka_decline in H.
  apply Nat.ltb_lt in H.
  unfold sigtuna_active, sigtuna_founded.
  apply Nat.leb_gt. lia.
Qed.

Theorem emporia_succession_conv :
  forall y, sigtuna_active y = true -> birka_active y = false.
Proof.
  intros y H. unfold sigtuna_active, sigtuna_founded in H.
  apply Nat.leb_le in H.
  unfold birka_active, birka_decline.
  apply Nat.ltb_ge. lia.
Qed.

Theorem emporia_never_coactive :
  forall y, birka_active y && sigtuna_active y = false.
Proof.
  intros y. destruct (birka_active y) eqn:E.
  - simpl. apply emporia_succession. exact E.
  - reflexivity.
Qed.
(* ================================================================== *)
(*  SECTION 3: MERCHANT TRADE PROVISIONS                               *)
(*  Per treaties of 911 and 944/945                                    *)
(* ================================================================== *)

(** The Rus' cities enumerated in the 911 and 944 texts, whose agents
    the treaties cover. *)
Inductive RusCity :=
  | Kiev
  | Chernigov
  | Pereyaslavl
  | Polotsk
  | Rostov
  | Liubech
  | OtherSettlement.  (* outside the treaty enumeration *)

Definition treaty_city (c : RusCity) : bool :=
  match c with
  | OtherSettlement => false
  | _               => true
  end.

Record MerchantParty := {
  party_size           : nat;
  has_princely_charter : bool;   (* Required from 944 onward *)
  ships                : nat;
  armed                : bool;
  home_city            : RusCity;
}.

(** Under the 944 treaty, merchants entering the city:
    - Must carry a charter (gramota) from the Kievan prince
    - May enter in groups of no more than 50
    - Must enter unarmed
    - Must lodge near the Monastery of St. Mamas
    - Stay limited to 6 months
    - Silk purchases capped at 50 bezants per person *)

Definition max_entry_group : nat := 50.
Definition max_stay_months : nat := 6.
Definition max_silk_bezants : nat := 50.

(** Provision flags, one per treaty article family. A flag is set only
    where the surviving text attests the provision. *)
Definition charter_required (t : Treaty) : bool :=
  match t with
  | Treaty_907 => false
  | Treaty_911 => false
  | Treaty_944 => true
  | Treaty_971 => true
  end.

Definition group_size_limited (t : Treaty) : bool :=
  match t with
  | Treaty_907 => false
  | Treaty_911 => false
  | Treaty_944 => true
  | Treaty_971 => true
  end.

Definition silk_capped (t : Treaty) : bool :=
  match t with
  | Treaty_944 | Treaty_971 => true
  | _ => false
  end.

Definition stay_limited (t : Treaty) : bool :=
  match t with
  | Treaty_944 | Treaty_971 => true
  | _ => false
  end.

(** Whether the treaty text confers merchant privileges at all. The
    971 document is a bare non-aggression oath extracted at Dorostolon
    and grants the Rus' nothing. *)
Definition grants_trade_privileges (t : Treaty) : bool :=
  match t with
  | Treaty_971 => false
  | _          => true
  end.

(** Benefits attested only in the 907 narrative: tribute, the
    mesyachina provisioning, and bath access. The 944 text renews the
    provisioning clause. *)
Definition tribute_paid (t : Treaty) : bool :=
  match t with
  | Treaty_907 => true
  | _          => false
  end.

Definition provisions_supplied (t : Treaty) : bool :=
  match t with
  | Treaty_907 | Treaty_944 => true
  | _ => false
  end.

Definition bath_access (t : Treaty) : bool :=
  match t with
  | Treaty_907 => true
  | _          => false
  end.

(** A merchant party is admissible to Miklagard under a given treaty. *)
Definition admissible (t : Treaty) (mp : MerchantParty) : bool :=
  grants_trade_privileges t
  && treaty_city (home_city mp)
  && (negb (charter_required t) || has_princely_charter mp)
  && (negb (group_size_limited t) || (party_size mp <=? max_entry_group))
  && (negb (group_size_limited t) || negb (armed mp))
  && (1 <=? ships mp).

(** Under the 911 treaty, any party with ships from a treaty city is
    admissible regardless of charter, size, or arms. *)
Theorem treaty_911_permissive :
  forall mp,
    treaty_city (home_city mp) = true ->
    ships mp >= 1 ->
    admissible Treaty_911 mp = true.
Proof.
  intros mp Hcity Hships.
  unfold admissible. simpl.
  rewrite Hcity. simpl.
  destruct (ships mp) eqn:Hs.
  - lia.
  - reflexivity.
Qed.

(** Under the 944 treaty, an armed party is never admissible. *)
Theorem treaty_944_disarms :
  forall mp,
    armed mp = true ->
    admissible Treaty_944 mp = false.
Proof.
  intros mp Harmed.
  unfold admissible. simpl.
  rewrite Harmed. simpl.
  rewrite andb_false_r.
  reflexivity.
Qed.

(** A chartered, unarmed party of 50 or fewer with ships, from a
    treaty city, is always admissible under the 944 treaty. *)
Theorem treaty_944_compliant_admitted :
  forall mp,
    treaty_city (home_city mp) = true ->
    has_princely_charter mp = true ->
    armed mp = false ->
    party_size mp <= 50 ->
    ships mp >= 1 ->
    admissible Treaty_944 mp = true.
Proof.
  intros mp Hcity Hcharter Hunarmed Hsize Hships.
  unfold admissible, max_entry_group. simpl.
  rewrite Hcity, Hcharter, Hunarmed. simpl.
  rewrite andb_true_r.
  apply andb_true_intro. split.
  - apply Nat.leb_le. lia.
  - destruct (ships mp) eqn:Hs; [lia | reflexivity].
Qed.

(** Necessary conditions, uniformly in the treaty. *)
Theorem admissible_needs_ships :
  forall t mp, admissible t mp = true -> 1 <= ships mp.
Proof.
  intros t mp H. unfold admissible in H.
  rewrite !andb_true_iff in H.
  destruct H as [_ Hs]. apply Nat.leb_le. exact Hs.
Qed.

Theorem admissible_needs_treaty_city :
  forall t mp, admissible t mp = true -> treaty_city (home_city mp) = true.
Proof.
  intros t mp H. unfold admissible in H.
  rewrite !andb_true_iff in H. tauto.
Qed.

Theorem non_treaty_city_inadmissible :
  forall t mp, home_city mp = OtherSettlement -> admissible t mp = false.
Proof.
  intros t mp H. unfold admissible. rewrite H.
  simpl. rewrite andb_false_r. reflexivity.
Qed.

(** Full characterizations: each check is necessary and they are
    jointly sufficient. *)
Theorem admissible_944_characterization :
  forall mp,
    admissible Treaty_944 mp = true <->
    (treaty_city (home_city mp) = true /\
     has_princely_charter mp = true /\
     party_size mp <= 50 /\
     armed mp = false /\
     1 <= ships mp).
Proof.
  intros mp. unfold admissible, max_entry_group. cbn -[Nat.leb].
  rewrite !andb_true_iff, !Nat.leb_le, negb_true_iff.
  intuition.
Qed.

Theorem admissible_911_characterization :
  forall mp,
    admissible Treaty_911 mp = true <->
    (treaty_city (home_city mp) = true /\ 1 <= ships mp).
Proof.
  intros mp. unfold admissible. cbn -[Nat.leb].
  rewrite !andb_true_iff, !Nat.leb_le.
  intuition.
Qed.

(** The 971 capitulation grants no admission at all. *)
Theorem no_admission_under_971 :
  forall mp, admissible Treaty_971 mp = false.
Proof. intros mp. reflexivity. Qed.

(** The 907 narrative and the 911 charter agree at the level of entry
    conditions; they separate at the level of granted benefits. *)
Theorem admissible_907_911_agree :
  forall mp, admissible Treaty_907 mp = admissible Treaty_911 mp.
Proof. intros mp. reflexivity. Qed.

(** Later treaties admit subsets of what earlier treaties admit. *)
Theorem admissible_antitone :
  forall t1 t2 mp,
    treaty_year t1 <= treaty_year t2 ->
    admissible t2 mp = true ->
    admissible t1 mp = true.
Proof.
  intros t1 t2 mp Hy H; destruct t1, t2; simpl in Hy; try lia; clear Hy;
  unfold admissible in *; simpl in *; try discriminate;
  rewrite !andb_true_iff in *; intuition.
Qed.

(** Strictness witnesses. Oleg-era raiders: one hundred armed men,
    no charter. Admissible in 911, inadmissible in 944. *)
Definition oleg_era_party : MerchantParty :=
  {| party_size := 100;
     has_princely_charter := false;
     ships := 20;
     armed := true;
     home_city := Kiev |}.

Theorem inclusion_911_944_strict :
  admissible Treaty_911 oleg_era_party = true /\
  admissible Treaty_944 oleg_era_party = false.
Proof. split; reflexivity. Qed.

(** A fully compliant party of the 944 regime, shut out by 971. *)
Definition igor_era_party : MerchantParty :=
  {| party_size := 40;
     has_princely_charter := true;
     ships := 5;
     armed := false;
     home_city := Chernigov |}.

Theorem inclusion_944_971_strict :
  admissible Treaty_944 igor_era_party = true /\
  admissible Treaty_971 igor_era_party = false.
Proof. split; reflexivity. Qed.

(* ================================================================== *)
(*  SECTION 4: SILK, SOJOURN, AND LAWFUL VISITS                        *)
(* ================================================================== *)

Definition silk_lawful (t : Treaty) (bezants : nat) : bool :=
  negb (silk_capped t) || (bezants <=? max_silk_bezants).

Definition stay_lawful (t : Treaty) (months : nat) : bool :=
  negb (stay_limited t) || (months <=? max_stay_months).

Theorem silk_cap_944 :
  forall b, silk_lawful Treaty_944 b = true <-> b <= 50.
Proof.
  intros b. unfold silk_lawful, max_silk_bezants. simpl.
  apply Nat.leb_le.
Qed.

Theorem silk_unbounded_911 :
  forall b, silk_lawful Treaty_911 b = true.
Proof. intros b. reflexivity. Qed.

Theorem stay_cap_944 :
  forall m, stay_lawful Treaty_944 m = true <-> m <= 6.
Proof.
  intros m. unfold stay_lawful, max_stay_months. simpl.
  apply Nat.leb_le.
Qed.

Theorem stay_unbounded_911 :
  forall m, stay_lawful Treaty_911 m = true.
Proof. intros m. reflexivity. Qed.

(** A visit joins the party with its purchases and its sojourn. *)
Record Visit := {
  visit_party  : MerchantParty;
  silk_bezants : nat;
  stay_length  : nat;
}.

Definition visit_lawful (t : Treaty) (v : Visit) : bool :=
  admissible t (visit_party v)
  && silk_lawful t (silk_bezants v)
  && stay_lawful t (stay_length v).

Theorem compliant_visit_944 :
  forall v,
    treaty_city (home_city (visit_party v)) = true ->
    has_princely_charter (visit_party v) = true ->
    armed (visit_party v) = false ->
    party_size (visit_party v) <= 50 ->
    ships (visit_party v) >= 1 ->
    silk_bezants v <= 50 ->
    stay_length v <= 6 ->
    visit_lawful Treaty_944 v = true.
Proof.
  intros v Hc Hch Ha Hs Hsh Hsilk Hstay.
  unfold visit_lawful.
  rewrite (treaty_944_compliant_admitted _ Hc Hch Ha Hs Hsh). simpl.
  unfold silk_lawful, stay_lawful. simpl.
  apply andb_true_intro. split; apply Nat.leb_le; assumption.
Qed.

Theorem lawful_visit_silk_bound :
  forall v, visit_lawful Treaty_944 v = true ->
    silk_bezants v <= max_silk_bezants.
Proof.
  intros v H. unfold visit_lawful in H.
  rewrite !andb_true_iff in H.
  destruct H as [[_ Hsilk] _].
  unfold silk_lawful in Hsilk. simpl in Hsilk.
  apply Nat.leb_le. exact Hsilk.
Qed.

Theorem lawful_visit_stay_bound :
  forall v, visit_lawful Treaty_944 v = true ->
    stay_length v <= max_stay_months.
Proof.
  intros v H. unfold visit_lawful in H.
  rewrite !andb_true_iff in H.
  destruct H as [_ Hstay].
  unfold stay_lawful in Hstay. simpl in Hstay.
  apply Nat.leb_le. exact Hstay.
Qed.

(* ================================================================== *)
(*  SECTION 5: TREATY FAVORABILITY, DERIVED FROM PROVISIONS            *)
(* ================================================================== *)

(** Favorability to the Rus' is not a bare table: it counts the
    attested benefits of each treaty. Absence of a restriction counts
    as a benefit, presence of tribute, provisioning, baths, and trade
    rights likewise. *)
Definition benefit_count (t : Treaty) : nat :=
  Nat.b2n (tribute_paid t)
  + Nat.b2n (provisions_supplied t)
  + Nat.b2n (bath_access t)
  + Nat.b2n (negb (charter_required t))
  + Nat.b2n (negb (group_size_limited t))
  + Nat.b2n (negb (silk_capped t))
  + Nat.b2n (negb (stay_limited t))
  + Nat.b2n (grants_trade_privileges t).

Definition treaty_favorability (t : Treaty) : nat := benefit_count t.

(** Treaty provisions become progressively less favorable to the
    Rus' over time, now proved from the provision flags rather than
    asserted. *)
Theorem treaties_less_favorable_over_time :
  forall t1 t2,
    treaty_year t1 < treaty_year t2 ->
    treaty_favorability t1 > treaty_favorability t2.
Proof.
  intros t1 t2 H.
  destruct t1, t2; simpl in H; compute; lia.
Qed.

(** The chain restricted to the diplomatic texts, free of the 907
    historicity dispute. *)
Theorem diplomatic_favorability_chain :
  forall t1 t2,
    treaty_source t1 = DiplomaticText ->
    treaty_source t2 = DiplomaticText ->
    treaty_year t1 < treaty_year t2 ->
    treaty_favorability t1 > treaty_favorability t2.
Proof.
  intros t1 t2 S1 S2 H.
  destruct t1, t2; simpl in S1, S2, H; try discriminate; compute; lia.
Qed.
(* ================================================================== *)
(*  SECTION 6: THE VARANGIAN GUARD                                     *)
(*  (Greek: Tagma ton Varangon)                                        *)
(*  Formally constituted 988 CE under Basil II.                        *)
(* ================================================================== *)

Definition guard_founded : year := 988.
Definition hastings : year := 1066.
Definition anglo_ascendancy : year := 1100.
Definition vladimir_contingent : nat := 6 * 1000.

Inductive GuardEra :=
  | PreFormal        (* Before 988: ad hoc Rus' mercenaries *)
  | NorseDominant    (* 988 - c.1066: primarily Scandinavian *)
  | TransitionEra    (* c.1066 - c.1100: mixed Norse/Anglo-Saxon *)
  | AngloSaxonDominant. (* c.1100 onward *)

Definition guard_era (y : year) : GuardEra :=
  if y <? guard_founded then PreFormal
  else if y <? hastings then NorseDominant
  else if y <? anglo_ascendancy then TransitionEra
  else AngloSaxonDominant.

Definition era_index (e : GuardEra) : nat :=
  match e with
  | PreFormal          => 0
  | NorseDominant      => 1
  | TransitionEra      => 2
  | AngloSaxonDominant => 3
  end.

(** Exact behavior at every boundary. *)
Theorem guard_era_boundaries :
  guard_era 987 = PreFormal /\
  guard_era 988 = NorseDominant /\
  guard_era 1065 = NorseDominant /\
  guard_era 1066 = TransitionEra /\
  guard_era 1099 = TransitionEra /\
  guard_era 1100 = AngloSaxonDominant.
Proof. repeat split; reflexivity. Qed.

Theorem preformal_era :
  forall y, y < guard_founded -> guard_era y = PreFormal.
Proof.
  intros y H. unfold guard_era.
  destruct (y <? guard_founded) eqn:E.
  - reflexivity.
  - apply Nat.ltb_ge in E. lia.
Qed.

(** Before Hastings (1066), the Guard is Norse. *)
Theorem pre_hastings_norse :
  forall y, guard_founded <= y -> y < hastings ->
    guard_era y = NorseDominant.
Proof.
  intros y H1 H2.
  unfold guard_era.
  destruct (y <? guard_founded) eqn:E1.
  - apply Nat.ltb_lt in E1. lia.
  - destruct (y <? hastings) eqn:E2.
    + reflexivity.
    + apply Nat.ltb_ge in E2. lia.
Qed.

Theorem post_hastings_transition :
  forall y, hastings <= y -> y < anglo_ascendancy ->
    guard_era y = TransitionEra.
Proof.
  intros y H1 H2.
  unfold guard_era, guard_founded, hastings, anglo_ascendancy in *.
  destruct (y <? 988) eqn:E1.
  - apply Nat.ltb_lt in E1. lia.
  - destruct (y <? 1066) eqn:E2.
    + apply Nat.ltb_lt in E2. lia.
    + destruct (y <? 1100) eqn:E3.
      * reflexivity.
      * apply Nat.ltb_ge in E3. lia.
Qed.

Theorem anglo_ascendancy_era :
  forall y, anglo_ascendancy <= y -> guard_era y = AngloSaxonDominant.
Proof.
  intros y H.
  unfold guard_era, guard_founded, hastings, anglo_ascendancy in *.
  destruct (y <? 988) eqn:E1; [apply Nat.ltb_lt in E1; lia|].
  destruct (y <? 1066) eqn:E2; [apply Nat.ltb_lt in E2; lia|].
  destruct (y <? 1100) eqn:E3; [apply Nat.ltb_lt in E3; lia|].
  reflexivity.
Qed.

(** The era classification is total and monotone in time. *)
Theorem guard_era_total :
  forall y, guard_era y = PreFormal \/ guard_era y = NorseDominant \/
            guard_era y = TransitionEra \/ guard_era y = AngloSaxonDominant.
Proof.
  intros y. unfold guard_era.
  destruct (y <? guard_founded).
  - left; reflexivity.
  - destruct (y <? hastings).
    + right; left; reflexivity.
    + destruct (y <? anglo_ascendancy).
      * right; right; left; reflexivity.
      * right; right; right; reflexivity.
Qed.

Theorem guard_era_monotone :
  forall y1 y2, y1 <= y2 ->
    era_index (guard_era y1) <= era_index (guard_era y2).
Proof.
  intros y1 y2 Hle.
  unfold guard_era, guard_founded, hastings, anglo_ascendancy, era_index.
  destruct (y1 <? 988) eqn:A1; destruct (y2 <? 988) eqn:A2;
  destruct (y1 <? 1066) eqn:B1; destruct (y2 <? 1066) eqn:B2;
  destruct (y1 <? 1100) eqn:C1; destruct (y2 <? 1100) eqn:C2;
  simpl;
  repeat match goal with
         | H : (_ <? _) = true |- _ => apply Nat.ltb_lt in H
         | H : (_ <? _) = false |- _ => apply Nat.ltb_ge in H
         end;
  lia.
Qed.

Inductive OathType :=
  | OathPerun     (* Pagan: weapons laid down, sworn by Perun *)
  | OathCross     (* Christian: sworn on the Cross *)
  | OathAxe.      (* Varangian service oath on the battle-axe *)

Record Varangian := {
  name        : nat;  (* abstract identifier *)
  origin      : Civilization;
  religion    : Religion;
  oath        : OathType;
  entry_year  : year;
  entry_fee_nomismata : nat;  (* lump-sum payment for admission *)
}.

(** Origin composition tracks the historical shift. *)
Definition expected_origin (era : GuardEra) : Civilization :=
  match era with
  | PreFormal          => Rus
  | NorseDominant      => Norse
  | TransitionEra      => Norse   (* mixed, but still Norse-led *)
  | AngloSaxonDominant => AngloSaxon
  end.

Theorem composition_by_era :
  expected_origin PreFormal = Rus /\
  expected_origin NorseDominant = Norse /\
  expected_origin TransitionEra = Norse /\
  expected_origin AngloSaxonDominant = AngloSaxon.
Proof. repeat split; reflexivity. Qed.

Theorem norse_era_origin :
  forall y, guard_founded <= y -> y < hastings ->
    expected_origin (guard_era y) = Norse.
Proof.
  intros y H1 H2. rewrite (pre_hastings_norse y H1 H2). reflexivity.
Qed.

Theorem anglo_era_origin :
  forall y, anglo_ascendancy <= y ->
    expected_origin (guard_era y) = AngloSaxon.
Proof.
  intros y H. rewrite (anglo_ascendancy_era y H). reflexivity.
Qed.

(** Rosters: composition as a proved property of member lists. *)
Definition civ_eqb (a b : Civilization) : bool :=
  match a, b with
  | Norse, Norse | Rus, Rus | Byzantine, Byzantine
  | AngloSaxon, AngloSaxon | Norman, Norman => true
  | _, _ => false
  end.

Definition Roster := list Varangian.

Definition count_origin (c : Civilization) (r : Roster) : nat :=
  length (filter (fun v => civ_eqb (origin v) c) r).

Definition majority_origin (c : Civilization) (r : Roster) : bool :=
  length r <? 2 * count_origin c r.

Lemma all_norse_count :
  forall r : Roster,
    Forall (fun v => origin v = Norse) r ->
    count_origin Norse r = length r.
Proof.
  induction r as [|v r IH]; intros Hall.
  - reflexivity.
  - inversion Hall as [|? ? Hv Hrest]; subst.
    unfold count_origin in *. simpl. rewrite Hv. simpl.
    f_equal. apply IH. assumption.
Qed.

Theorem norse_roster_majority :
  forall r : Roster,
    r <> [] ->
    Forall (fun v => origin v = Norse) r ->
    majority_origin Norse r = true.
Proof.
  intros r Hne Hall. unfold majority_origin.
  rewrite (all_norse_count r Hall).
  apply Nat.ltb_lt.
  destruct r; [congruence | simpl; lia].
Qed.

(* ================================================================== *)
(*  SECTION 7: HARALD, EMPERORS, POLUTASVARF, PAY                      *)
(* ================================================================== *)

(** Harald Sigurdsson (Hardrada) served c. 1034-1042, squarely in the
    Norse-dominant era. *)
Definition harald_service_start : year := 1034.
Definition harald_service_end : year := 1042.

Definition harald : Varangian :=
  {| name := 1;
     origin := Norse;
     religion := ChristianOrthodox;
     oath := OathAxe;
     entry_year := harald_service_start;
     entry_fee_nomismata := 0 |}.  (* unrecorded *)

Theorem harald_in_norse_era :
  guard_era harald_service_start = NorseDominant.
Proof. reflexivity. Qed.

Theorem harald_service_all_norse_era :
  forall y, harald_service_start <= y -> y <= harald_service_end ->
    guard_era y = NorseDominant.
Proof.
  intros y H1 H2.
  apply pre_hastings_norse;
  unfold harald_service_start, harald_service_end,
         guard_founded, hastings in *; lia.
Qed.

(** The Battle of Manzikert (1071): virtually all Guards fell. *)
Definition manzikert : year := 1071.

Theorem manzikert_in_transition :
  guard_era manzikert = TransitionEra.
Proof. reflexivity. Qed.

(** Emperors of Harald's period. reign_end covers death or
    deposition; polutasvarf attaches to the transition. *)
Inductive Emperor :=
  | BasilII      (* d. 1025 *)
  | RomanosIII   (* d. 1034 *)
  | MichaelIV    (* d. 1041 *)
  | MichaelV.    (* deposed 1042 *)

Definition reign_end (e : Emperor) : year :=
  match e with
  | BasilII    => 1025
  | RomanosIII => 1034
  | MichaelIV  => 1041
  | MichaelV   => 1042
  end.

Definition emperors : list Emperor :=
  [BasilII; RomanosIII; MichaelIV; MichaelV].

Definition serves_during (entry leave y : year) : bool :=
  (entry <=? y) && (y <=? leave).

(** Polutasvarf: upon the emperor's death, each guardsman then in
    service may take gold from the imperial treasury. Eligibility is
    presence in service at the transition, not entry date. *)
Inductive PolutasvarfEligible (entry leave death : year) : Prop :=
  | polutasvarf_rule :
      serves_during entry leave death = true ->
      PolutasvarfEligible entry leave death.

(** Snorri reports Harald took part in polutasvarf three times. Of
    the four reign ends encoded, exactly the three inside his service
    window qualify; Basil II's death (1025) precedes it. *)
Theorem harald_three_polutasvarf :
  length (filter (serves_during (entry_year harald) harald_service_end)
                 (map reign_end emperors)) = 3.
Proof. reflexivity. Qed.

Theorem harald_eligible_michael_iv :
  PolutasvarfEligible (entry_year harald) harald_service_end
                      (reign_end MichaelIV).
Proof. constructor. reflexivity. Qed.

Theorem basil_death_precedes_harald :
  serves_during (entry_year harald) harald_service_end
                (reign_end BasilII) = false.
Proof. reflexivity. Qed.

(** The Vastgotalagen provision: a man serving in 'Greece' (= the
    Byzantine Empire) cannot inherit while abroad. The law is West
    Geatish; Norse origin is the granularity carried here. *)
Definition vastgotalagen_disinherits (v : Varangian) : bool :=
  match origin v with
  | Norse => true
  | _     => false
  end.

Theorem vastgotalagen_characterization :
  forall v, vastgotalagen_disinherits v = true <-> origin v = Norse.
Proof.
  intros v. unfold vastgotalagen_disinherits.
  destruct (origin v); split; intro Hx;
    first [reflexivity | discriminate].
Qed.

Theorem harald_disinherited :
  vastgotalagen_disinherits harald = true.
Proof. reflexivity. Qed.

(** Pay evidence. De Ceremoniis (Constantine VII) records the Cretan
    expedition payroll (dated 902 or 911 in the literature): 700 Rus'
    paid 100 litrai in aggregate, at 72 nomismata to the litra. The
    monthly palace and field scales are modern estimates in the
    Blondal and Benedikz tradition, not De Ceremoniis figures. *)
Definition palace_monthly_pay : nat := 40.
Definition field_monthly_pay_low : nat := 10.
Definition field_monthly_pay_high : nat := 15.

Definition nomismata_per_litra : nat := 72.
Definition cretan_rus_contingent : nat := 700.
Definition cretan_payroll_litrai : nat := 100.
Definition cretan_total_nomismata : nat :=
  cretan_payroll_litrai * nomismata_per_litra.
Definition cretan_per_man : nat :=
  cretan_total_nomismata / cretan_rus_contingent.

Theorem cretan_per_man_value : cretan_per_man = 10.
Proof. reflexivity. Qed.

(** Exact division check: 10 per man leaves a remainder of 200
    nomismata on the aggregate. *)
Theorem cretan_division :
  cretan_per_man * cretan_rus_contingent + 200 = cretan_total_nomismata.
Proof. reflexivity. Qed.

Theorem cretan_within_field_band :
  field_monthly_pay_low <= cretan_per_man <= field_monthly_pay_high.
Proof. compute. lia. Qed.

Theorem pay_band_nonempty :
  field_monthly_pay_low <= field_monthly_pay_high.
Proof. compute. lia. Qed.

Theorem palace_exceeds_field :
  field_monthly_pay_high < palace_monthly_pay.
Proof. compute. lia. Qed.

(* ================================================================== *)
(*  SECTION 8: GUARD FOUNDING                                          *)
(* ================================================================== *)

Record GuardFounding := {
  founding_year    : year;
  founding_size    : nat;
  founding_emperor : Emperor;
}.

(** Vladimir's contingent of 6,000, sent to Basil II. *)
Definition guard_founding : GuardFounding :=
  {| founding_year := guard_founded;
     founding_size := vladimir_contingent;
     founding_emperor := BasilII |}.

Theorem founding_opens_norse_era :
  guard_era (founding_year guard_founding) = NorseDominant.
Proof. reflexivity. Qed.

Theorem founding_within_basil_reign :
  founding_year guard_founding <= reign_end (founding_emperor guard_founding).
Proof. compute. lia. Qed.

Theorem pre_founding_preformal :
  forall y, y < founding_year guard_founding -> guard_era y = PreFormal.
Proof.
  intros y Hy. unfold guard_founding in Hy. simpl in Hy.
  apply preformal_era. exact Hy.
Qed.

Theorem contingent_dwarfs_cretan :
  cretan_rus_contingent < vladimir_contingent.
Proof. compute. lia. Qed.
(* ================================================================== *)
(*  SECTION 9: TREATY CRIMINAL LAW PROVISIONS                          *)
(*  Articles 3-7 of the 911 treaty                                     *)
(* ================================================================== *)

Inductive Crime :=
  | Murder
  | IntentionalAssault
  | Theft
  | Robbery
  | DebtDefault.

Inductive Penalty :=
  | DeathAtScene       (* Murder: kinsman may kill at the spot *)
  | PropertyForfeit    (* Assault/theft/robbery: fine or restitution *)
  | Imprisonment       (* Captivity pending ransom *)
  | Extradition.       (* Fugitive return *)

(** The 911 treaty writes each article twice over, once for a Rus'
    offender against a Greek and once for a Greek offender against a
    Rus'. The two tables are encoded separately, as the text runs, and
    proved extensionally equal. A fleeing debtor is returned. *)
Definition penalty_on_rus_offender (c : Crime) : Penalty :=
  match c with
  | Murder             => DeathAtScene
  | IntentionalAssault => PropertyForfeit
  | Theft              => PropertyForfeit
  | Robbery            => PropertyForfeit
  | DebtDefault        => Extradition
  end.

Definition penalty_on_byzantine_offender (c : Crime) : Penalty :=
  match c with
  | Murder             => DeathAtScene
  | IntentionalAssault => PropertyForfeit
  | Theft              => PropertyForfeit
  | Robbery            => PropertyForfeit
  | DebtDefault        => Extradition
  end.

(** Reciprocity as an equation between the two article tables. *)
Theorem criminal_reciprocity :
  forall c, penalty_on_rus_offender c = penalty_on_byzantine_offender c.
Proof. destruct c; reflexivity. Qed.

(** Jurisdiction: the treaty binds the two parties and no one else. *)
Definition treaty_911_penalty (offender : Civilization) (c : Crime)
  : option Penalty :=
  match offender with
  | Rus       => Some (penalty_on_rus_offender c)
  | Byzantine => Some (penalty_on_byzantine_offender c)
  | _         => None
  end.

Theorem reciprocity_in_force :
  forall c p1 p2,
    treaty_911_penalty Rus c = Some p1 ->
    treaty_911_penalty Byzantine c = Some p2 ->
    p1 = p2.
Proof.
  intros c p1 p2 H1 H2. simpl in H1, H2.
  inversion H1; inversion H2; subst.
  apply criminal_reciprocity.
Qed.

Theorem nonparties_outside_jurisdiction :
  forall c,
    treaty_911_penalty Norse c = None /\
    treaty_911_penalty AngloSaxon c = None /\
    treaty_911_penalty Norman c = None.
Proof. intros c. repeat split; reflexivity. Qed.

(* ================================================================== *)
(*  SECTION 10: CAPTIVES AND RANSOM                                    *)
(*  Articles 9-11 of the 911 treaty; the 944 scale                     *)
(* ================================================================== *)

(** A captive is held pending ransom and released on payment. *)
Definition captive_disposition (ransom_paid : bool) : Penalty :=
  if ransom_paid then Extradition else Imprisonment.

Theorem captive_release :
  captive_disposition true = Extradition /\
  captive_disposition false = Imprisonment.
Proof. split; reflexivity. Qed.

(** Every penalty the treaty names is realized by some case. *)
Theorem penalty_constructors_realized :
  forall p : Penalty,
    (exists c, penalty_on_rus_offender c = p) \/
    (exists b, captive_disposition b = p).
Proof.
  destruct p.
  - left; exists Murder; reflexivity.
  - left; exists Theft; reflexivity.
  - right; exists false; reflexivity.
  - left; exists DebtDefault; reflexivity.
Qed.

(** Ransom rates: 20 gold pieces under 911; the 944 treaty cuts the
    scale to 10 for the young, 8 for the middle-aged, 5 for the old
    and for children. The decline tracks the worsening terms. *)
Definition ransom_gold_911 : nat := 20.
Definition ransom_youth_944 : nat := 10.
Definition ransom_middle_944 : nat := 8.
Definition ransom_elder_944 : nat := 5.

Theorem ransom_scale_declines :
  ransom_youth_944 < ransom_gold_911 /\
  ransom_middle_944 < ransom_youth_944 /\
  ransom_elder_944 < ransom_middle_944.
Proof.
  unfold ransom_gold_911, ransom_youth_944,
         ransom_middle_944, ransom_elder_944.
  repeat split; lia.
Qed.

(* ================================================================== *)
(*  SECTION 11: MARITIME LAW                                           *)
(*  Article 8 of the 911 treaty; Article 2 of the 944 treaty           *)
(*  Based on the Rhodian Sea Law tradition                             *)
(* ================================================================== *)

Inductive ShipStatus :=
  | Sailing
  | Wrecked
  | Detained.  (* By weather or obstacle *)

Inductive ShoreProximity :=
  | NearRusTerritory
  | NearByzantineTerritory
  | OpenSea.

(** Under Article 8 (911): a wrecked or detained ship obliges the
    nearest party to render aid; a sailing ship obliges no one. *)
Definition salvage_required (s : ShipStatus) : bool :=
  match s with
  | Wrecked | Detained => true
  | Sailing => false
  end.

Definition salvage_duty (proximity : ShoreProximity) : Civilization :=
  match proximity with
  | NearRusTerritory       => Rus
  | NearByzantineTerritory => Byzantine
  | OpenSea                => Byzantine  (* Default to imperial authority *)
  end.

Theorem salvage_trigger_characterization :
  forall s, salvage_required s = false <-> s = Sailing.
Proof.
  intros s; destruct s; split; intro H;
    first [reflexivity | discriminate].
Qed.

Theorem salvage_duty_is_party :
  forall p s, salvage_required s = true ->
    salvage_duty p = Rus \/ salvage_duty p = Byzantine.
Proof.
  intros p s H; destruct p.
  - left; reflexivity.
  - right; reflexivity.
  - right; reflexivity.
Qed.

Theorem salvage_reciprocal :
  salvage_duty NearRusTerritory = Rus /\
  salvage_duty NearByzantineTerritory = Byzantine.
Proof. split; reflexivity. Qed.

(** The 944 treaty adds: ships without a princely charter may be
    apprehended by imperial authorities. *)
Definition ship_apprehensible (t : Treaty) (has_charter : bool) : bool :=
  charter_required t && negb has_charter.

Theorem unchartered_under_944_apprehensible :
  ship_apprehensible Treaty_944 false = true.
Proof. reflexivity. Qed.

Theorem chartered_under_944_safe :
  ship_apprehensible Treaty_944 true = false.
Proof. reflexivity. Qed.

Theorem pre_944_always_safe :
  forall b, ship_apprehensible Treaty_911 b = false.
Proof. intros []; reflexivity. Qed.

(* ================================================================== *)
(*  SECTION 12: CHERSONESOS AND WINTERING                              *)
(*  Article 8 of the 944 treaty; the 971 oath                          *)
(* ================================================================== *)

(** The Crimean exclave of Chersonesos is protected under the 944
    treaty, and the 971 oath renews the pledge: Sviatoslav swears not
    to march against the country of Kherson. *)
Inductive CrimeanZone :=
  | Chersonesos        (* Byzantine exclave *)
  | Beloberezhye_Zone  (* Jointly administered Dnieper mouth *)
  | Tmutarakan.        (* Rus'-controlled Taman Peninsula *)

Definition protected_zone (t : Treaty) (z : CrimeanZone) : bool :=
  match t, z with
  | Treaty_944, Chersonesos | Treaty_971, Chersonesos => true
  | _, _ => false
  end.

(** Wintering: the 944 treaty forbids the Rus' to winter at
    Beloberezhye; Chersonesos is a Byzantine city and never a Rus'
    wintering site; Tmutarakan is their own. The 971 oath does not
    restate the wintering ban, and Sviatoslav in fact wintered at
    Beloberezhye in 971-972. *)
Definition winter_permitted (t : Treaty) (z : CrimeanZone) : bool :=
  match z with
  | Chersonesos       => false
  | Beloberezhye_Zone => negb (match t with Treaty_944 => true | _ => false end)
  | Tmutarakan        => true
  end.

Theorem chersonesos_protected_944 :
  protected_zone Treaty_944 Chersonesos = true.
Proof. reflexivity. Qed.

Theorem chersonesos_protected_971 :
  protected_zone Treaty_971 Chersonesos = true.
Proof. reflexivity. Qed.

Theorem protection_monotone_from_944 :
  forall t, 944 <= treaty_year t -> protected_zone t Chersonesos = true.
Proof.
  intros t H; destruct t; simpl in H; try lia; reflexivity.
Qed.

Theorem protected_never_winterable :
  forall t z, protected_zone t z = true -> winter_permitted t z = false.
Proof.
  intros t z H; destruct t, z; simpl in *;
    first [reflexivity | discriminate].
Qed.

Theorem beloberezhye_ban_944 :
  winter_permitted Treaty_944 Beloberezhye_Zone = false.
Proof. reflexivity. Qed.

Theorem beloberezhye_free_911 :
  winter_permitted Treaty_911 Beloberezhye_Zone = true.
Proof. reflexivity. Qed.

Theorem sviatoslav_wintering_lawful_971 :
  winter_permitted Treaty_971 Beloberezhye_Zone = true.
Proof. reflexivity. Qed.

(* ================================================================== *)
(*  SECTION 13: THE OATH FRAMEWORK                                     *)
(*  Dual-oath structure of the 944 treaty                              *)
(* ================================================================== *)

(** The 944 treaty records a dual swearing:
    - Christian Rus' envoys swore on the Cross in the Church of St. Elias
    - Pagan Rus' envoys laid down weapons and swore by Perun
    This indicates partial Christianization ~44 years before 988. *)

Definition oath_for_religion (r : Religion) : OathType :=
  match r with
  | ChristianOrthodox => OathCross
  | NorsePagan        => OathPerun
  | ChristianLatin    => OathCross
  end.

(** Both oath types are equally binding under the treaty. *)
Inductive TreatyBinding : OathType -> Prop :=
  | binding_perun : TreatyBinding OathPerun
  | binding_cross : TreatyBinding OathCross.

Theorem all_treaty_oaths_bind :
  forall r, TreatyBinding (oath_for_religion r).
Proof. intros r; destruct r; simpl; constructor. Qed.

Theorem treaty_oath_never_axe :
  forall r, oath_for_religion r <> OathAxe.
Proof. intros r; destruct r; simpl; discriminate. Qed.

(** The axe oath is exactly the oath outside the treaty framework. *)
Theorem treaty_binding_characterization :
  forall o, TreatyBinding o <-> o <> OathAxe.
Proof.
  intros o; split.
  - intros Hb; destruct Hb; discriminate.
  - intros Hne; destruct o; [constructor | constructor | congruence].
Qed.

(* ================================================================== *)
(*  SECTION 14: ENVOY NAMES - NORSE ATTESTATION                        *)
(*  The 911 envoy roster and the 944 principals as data.               *)
(* ================================================================== *)

Inductive NameLanguage :=
  | NorseName
  | SlavicName.

(** The fifteen envoys of 911 (Cross and Sherbowitz-Wetzor
    normalization), and the 944 principals on whose behalf envoys
    came: Igor (Ingvarr), Olga (Helga), Akun (Hakon), and the first
    Slavic-named members of the dynastic circle. *)
Inductive PersonName :=
  | Karl | Ingjald | Farulf | Vermund | Hrollaf
  | Gunnar | Harold | Kami | Frithleif | Hroarr
  | Angantyr | Throand | Leithulf | Fast | Steinvith
  | Igor | Olga | Akun
  | Sviatoslav | Volodislav | Peredslava.

Definition name_language (n : PersonName) : NameLanguage :=
  match n with
  | Sviatoslav | Volodislav | Peredslava => SlavicName
  | _ => NorseName
  end.

Definition envoys_911 : list PersonName :=
  [Karl; Ingjald; Farulf; Vermund; Hrollaf;
   Gunnar; Harold; Kami; Frithleif; Hroarr;
   Angantyr; Throand; Leithulf; Fast; Steinvith].

Definition principals_944 : list PersonName :=
  [Igor; Olga; Akun; Sviatoslav; Volodislav; Peredslava].

Definition envoy_count_911 : nat := length envoys_911.

(** The 944 treaty names "no fewer than fifty" envoys and merchants. *)
Definition envoy_count_944_minimum : nat := 50.

Theorem envoy_count_911_value : envoy_count_911 = 15.
Proof. reflexivity. Qed.

(** Every 911 envoy bears a Norse name. *)
Theorem envoys_911_all_norse :
  Forall (fun n => name_language n = NorseName) envoys_911.
Proof. repeat constructor. Qed.

(** By 944 the dynastic circle carries Slavic names: the gradual
    Slavicization of the Kievan elite. *)
Theorem slavic_presence_944 :
  Exists (fun n => name_language n = SlavicName) principals_944.
Proof.
  apply Exists_exists. exists Sviatoslav. split.
  - simpl. repeat (first [left; reflexivity | right]).
  - reflexivity.
Qed.

Theorem envoy_growth :
  envoy_count_911 < envoy_count_944_minimum.
Proof. compute. lia. Qed.
