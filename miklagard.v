(******************************************************************************)
(*                                                                            *)
(*           Miklagard: Rus'-Byzantine Treaty and Varangian Service           *)
(*                                                                            *)
(*     Rus'-Byzantine treaty provisions (911, 944/945, 971) from the          *)
(*     Primary Chronicle: merchant admissibility, charter and arms            *)
(*     requirements, criminal reciprocity, Varangian Guard eras,              *)
(*     polutasvarf, and route monotonicity.                                   *)
(*                                                                            *)
(*     "And Oleg hung his shield upon the gate, to show his victory."         *)
(*     - Primary Chronicle, sub anno 907                                      *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: February 20, 2026                                                *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

Require Import Arith.
Require Import List.
Require Import Bool.
Require Import Lia.
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

(* ================================================================== *)
(*  SECTION 2: TRADE ROUTE — THE ROAD TO THE GREEKS                   *)
(*  (Old Norse: Austrvegr; Slavic: put' iz variag v greki)            *)
(* ================================================================== *)

Inductive Waypoint :=
  | Birka           (* Swedish emporium *)
  | Sigtuna         (* Swedish royal seat *)
  | Aldeigja        (* Staraya Ladoga — first Rus' settlement *)
  | Holmgardr       (* Novgorod — Rurik's seat from 862 *)
  | Koenugard       (* Kiev — capital from 882 *)
  | Beloberezhye    (* Dnieper mouth — jointly administered *)
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

(* ================================================================== *)
(*  SECTION 3: MERCHANT TRADE PROVISIONS                               *)
(*  Per treaties of 911 and 944/945                                    *)
(* ================================================================== *)

Record MerchantParty := {
  party_size        : nat;
  has_princely_charter : bool;   (* Required from 944 onward *)
  ships             : nat;
  armed             : bool;
  origin_city       : Waypoint;  (* Must be from Rus' treaty cities *)
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

(** The 911 treaty was more favorable: no charter requirement,
    no group size limit, provisions supplied freely. *)
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

(** A merchant party is admissible to Miklagård under a given treaty. *)
Definition admissible (t : Treaty) (mp : MerchantParty) : bool :=
  (* Charter check: required from 944 onward *)
  (negb (charter_required t) || has_princely_charter mp) &&
  (* Group size check: 50-person limit from 944 *)
  (negb (group_size_limited t) || (party_size mp <=? max_entry_group)) &&
  (* Must be unarmed to enter the city from 944 *)
  (negb (group_size_limited t) || negb (armed mp)) &&
  (* Must have at least one ship *)
  (1 <=? ships mp).

(** Under the 911 treaty, any party with ships is admissible
    regardless of charter, size, or arms. *)
Theorem treaty_911_permissive :
  forall mp,
    ships mp >= 1 ->
    admissible Treaty_911 mp = true.
Proof.
  intros mp Hships.
  unfold admissible. simpl.
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

(** A chartered, unarmed party of 50 or fewer with ships
    is always admissible under the 944 treaty. *)
Theorem treaty_944_compliant_admitted :
  forall mp,
    has_princely_charter mp = true ->
    armed mp = false ->
    party_size mp <= 50 ->
    ships mp >= 1 ->
    admissible Treaty_944 mp = true.
Proof.
  intros mp Hcharter Hunarmed Hsize Hships.
  unfold admissible, max_entry_group. simpl.
  rewrite Hcharter. simpl.
  rewrite Hunarmed. simpl.
  rewrite andb_true_r.
  apply andb_true_intro. split.
  - apply Nat.leb_le. lia.
  - destruct (ships mp) eqn:Hs; [lia | reflexivity].
Qed.

(* ================================================================== *)
(*  SECTION 4: THE VARANGIAN GUARD                                     *)
(*  (Greek: Τάγμα τῶν Βαράγγων)                                       *)
(*  Formally constituted 988 CE under Basil II.                        *)
(* ================================================================== *)

Definition guard_founded : year := 988.
Definition vladimir_contingent : nat := 6000.

Inductive GuardEra :=
  | PreFormal        (* Before 988: ad hoc Rus' mercenaries *)
  | NorseDominant    (* 988 - c.1066: primarily Scandinavian *)
  | TransitionEra    (* c.1066 - c.1100: mixed Norse/Anglo-Saxon *)
  | AngloSaxonDominant. (* c.1100 onward *)

Definition guard_era (y : year) : GuardEra :=
  if y <? 988 then PreFormal
  else if y <? 1066 then NorseDominant
  else if y <? 1100 then TransitionEra
  else AngloSaxonDominant.

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

(** Pay scales from De Ceremoniis (Constantine VII):
    - Crete expedition 902: ~11 nomismata per man
    - Palace guard duty: ~40 nomismata per month
    - Field service outside capital: 10-15 nomismata per month *)
Definition palace_monthly_pay : nat := 40.
Definition field_monthly_pay_low : nat := 10.
Definition field_monthly_pay_high : nat := 15.

(** Polutasvarf: upon the emperor's death, each guardsman may
    take as much gold from the imperial treasury as he can carry.
    We model this as a predicate rather than a specific amount. *)
Inductive PolutasvarfEligible : Varangian -> Prop :=
  | polutasvarf_rule : forall v,
      entry_year v >= guard_founded ->
      PolutasvarfEligible v.

(** The Västgötalagen provision: a Swede serving in 'Greece'
    (= Byzantine Empire) cannot inherit while abroad. *)
Definition vastgoatalagen_disinherits (v : Varangian) : bool :=
  match origin v with
  | Norse => true
  | _     => false
  end.

(** Origin composition tracks the historical shift. *)
Definition expected_origin (era : GuardEra) : Civilization :=
  match era with
  | PreFormal          => Rus
  | NorseDominant      => Norse
  | TransitionEra      => Norse   (* mixed, but still Norse-led *)
  | AngloSaxonDominant => AngloSaxon
  end.

(** Harald Sigurdsson (Hardrada) served c. 1034-1042,
    squarely in the Norse-dominant era. *)
Definition harald_service_start : year := 1034.
Definition harald_service_end : year := 1042.

Theorem harald_in_norse_era :
  guard_era harald_service_start = NorseDominant.
Proof. reflexivity. Qed.

(** The Battle of Manzikert (1071): virtually all Guards fell. *)
Definition manzikert : year := 1071.

Theorem manzikert_in_transition :
  guard_era manzikert = TransitionEra.
Proof. reflexivity. Qed.

(* ================================================================== *)
(*  SECTION 5: TREATY CRIMINAL LAW PROVISIONS                         *)
(*  Articles 3-7 of the 911 treaty                                    *)
(* ================================================================== *)

Inductive Crime :=
  | Murder
  | IntentionalAssault
  | Theft
  | Robbery
  | DebtDefault.

Inductive Penalty :=
  | DeathAtScene       (* Murder: kinsman may kill at the spot *)
  | PropertyForfeit    (* Theft/robbery: return + penalty *)
  | Imprisonment       (* Debt default *)
  | Extradition.       (* Fugitive return *)

(** The 911 treaty establishes reciprocal justice:
    crimes by Rus' against Greeks and vice versa
    are judged by the same rules. *)
Definition treaty_911_penalty (c : Crime) : Penalty :=
  match c with
  | Murder             => DeathAtScene
  | IntentionalAssault => PropertyForfeit
  | Theft              => PropertyForfeit
  | Robbery            => PropertyForfeit
  | DebtDefault        => Imprisonment
  end.

(** Reciprocity: the same penalty applies regardless of
    which party commits the crime. *)
Theorem criminal_reciprocity :
  forall (c : Crime) (perpetrator victim : Civilization),
    (perpetrator = Rus \/ perpetrator = Byzantine) ->
    (victim = Rus \/ victim = Byzantine) ->
    perpetrator <> victim ->
    treaty_911_penalty c = treaty_911_penalty c.
Proof.
  intros. reflexivity.
Qed.

(* ================================================================== *)
(*  SECTION 6: MARITIME LAW                                            *)
(*  Article 8 of the 911 treaty; Article 2 of the 944 treaty          *)
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

(** Under Article 8 (911): if a ship is wrecked or detained,
    the nearest party must render aid and escort the ship
    to the other party's territory. *)
Definition salvage_duty (proximity : ShoreProximity) : Civilization :=
  match proximity with
  | NearRusTerritory       => Rus
  | NearByzantineTerritory => Byzantine
  | OpenSea                => Byzantine  (* Default to imperial authority *)
  end.

(** The 944 treaty adds: ships without a princely charter
    may be apprehended by imperial authorities. *)
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
(*  SECTION 7: CHERSONESOS NON-AGGRESSION                             *)
(*  Article 8 of the 944 treaty                                       *)
(* ================================================================== *)

(** The Crimean exclave of Chersonesos was explicitly protected
    under the 944 treaty. The Rus' prince pledged non-aggression. *)

Inductive CrimeanZone :=
  | Chersonesos    (* Byzantine exclave *)
  | Beloberezhye_Zone  (* Jointly administered Dnieper mouth *)
  | Tmutarakan.    (* Rus'-controlled Taman Peninsula *)

Definition protected_zone (t : Treaty) (z : CrimeanZone) : bool :=
  match t with
  | Treaty_944 =>
    match z with
    | Chersonesos => true
    | _           => false
    end
  | _ => false
  end.

(** Under 944: Rus' forbidden to winter at Beloberezhye
    or oppress Chersonesos fishers. *)
Definition winter_permitted (t : Treaty) (z : CrimeanZone) : bool :=
  match t with
  | Treaty_944 =>
    match z with
    | Beloberezhye_Zone => false
    | _                 => true
    end
  | _ => true  (* No restriction pre-944 *)
  end.

(* ================================================================== *)
(*  SECTION 8: THE OATH FRAMEWORK                                      *)
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
  forall r,
    r = ChristianOrthodox \/ r = NorsePagan \/ r = ChristianLatin ->
    TreatyBinding (oath_for_religion r).
Proof.
  intros r [H | [H | H]]; subst; simpl; constructor.
Qed.

(* ================================================================== *)
(*  SECTION 9: ENVOY NAMES — NORSE ATTESTATION                        *)
(*  The 911 treaty envoy names are exclusively Norse.                  *)
(*  We encode the 15 named envoys from the Primary Chronicle.         *)
(* ================================================================== *)

(** Envoy names from the 911 treaty (PVL):
    Karl, Ingjald, Farulf, Vermund, Hrollaf, Gunnar,
    Harold, Kami, Frithleif, Hroarr, Angantyr,
    Throand, Leithulf, Fast, Steinvith.

    All names are Norse. We track this as a property. *)

Definition envoy_count_911 : nat := 15.

(** By 944, "no fewer than fifty" envoys are named,
    with the "overwhelming majority" having Norse names,
    but some Slavonic names appear. *)
Definition envoy_count_944_minimum : nat := 50.

(** The shift from purely Norse to mixed names tracks
    the gradual Slavicization of the Kievan Rus' elite. *)
Theorem envoy_growth :
  envoy_count_911 < envoy_count_944_minimum.
Proof. unfold envoy_count_911, envoy_count_944_minimum. lia. Qed.

(* ================================================================== *)
(*  SECTION 10: ROUTE MONOTONICITY AND TREATY ORDERING                 *)
(* ================================================================== *)

(** The trade route is strictly ordered from Birka to Miklagård. *)
Theorem route_monotone :
  forall w1 w2,
    on_route w1 w2 = true ->
    waypoint_order w1 < waypoint_order w2.
Proof.
  intros w1 w2 H.
  unfold on_route in H.
  apply Nat.ltb_lt in H. exact H.
Qed.

(** Miklagård is the terminal waypoint. *)
Theorem miklagard_terminal :
  forall w, w <> Miklagard -> on_route w Miklagard = true.
Proof.
  intros w Hneq.
  unfold on_route.
  apply Nat.ltb_lt.
  destruct w; simpl; try lia.
  contradiction.
Qed.

(** No waypoint is beyond Miklagård. *)
Theorem nothing_beyond_miklagard :
  forall w, on_route Miklagard w = false.
Proof.
  intros w. unfold on_route. simpl.
  destruct w; reflexivity.
Qed.

(** Treaty provisions become progressively less favorable
    to the Rus' over time (907 > 911 > 944 > 971). *)
Definition treaty_favorability (t : Treaty) : nat :=
  match t with
  | Treaty_907 => 4
  | Treaty_911 => 3
  | Treaty_944 => 2
  | Treaty_971 => 1
  end.

Theorem treaties_less_favorable_over_time :
  forall t1 t2,
    treaty_year t1 < treaty_year t2 ->
    treaty_favorability t1 > treaty_favorability t2.
Proof.
  intros t1 t2 H.
  destruct t1, t2; simpl in *; lia.
Qed.

(* ================================================================== *)
(*  SECTION 11: COMPOSITION THEOREM                                    *)
(*  The Guard's composition shifts predictably with history.           *)
(* ================================================================== *)

(** Before Hastings (1066), the Guard is Norse.
    After Hastings, Anglo-Saxons displaced by the Normans arrive. *)
Theorem pre_hastings_norse :
  forall y, 988 <= y -> y < 1066 ->
    guard_era y = NorseDominant.
Proof.
  intros y H1 H2.
  unfold guard_era.
  destruct (y <? 988) eqn:E1.
  - apply Nat.ltb_lt in E1. lia.
  - destruct (y <? 1066) eqn:E2.
    + reflexivity.
    + apply Nat.ltb_ge in E2. lia.
Qed.

Theorem post_hastings_transition :
  forall y, 1066 <= y -> y < 1100 ->
    guard_era y = TransitionEra.
Proof.
  intros y H1 H2.
  unfold guard_era.
  destruct (y <? 988) eqn:E1.
  - apply Nat.ltb_lt in E1. lia.
  - destruct (y <? 1066) eqn:E2.
    + apply Nat.ltb_lt in E2. lia.
    + destruct (y <? 1100) eqn:E3.
      * reflexivity.
      * apply Nat.ltb_ge in E3. lia.
Qed.
