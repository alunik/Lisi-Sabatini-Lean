module

public import LisiSabatini.FiniteCertificates.A8Rows
public import LisiSabatini.FiniteCertificates.FingerprintCheck

/-!
# Small conservative fingerprints for the A8 rows

Generated data only: all mask-coverage proofs below use kernel evaluation.
A hash collision can reject an additional conjugator but cannot accept an
incorrect one. The resulting bounds are 2218, 276, 26, and 16.
-/

@[expose] public section

namespace LisiSabatini.FiniteCertificates.A8FingerprintData

open A8Rows

abbrev G := A8Rows.G

local instance : DecidableEq G := alternatingCodeDecidableEq_fin8

set_option maxRecDepth 100000

/-- Eight-image base-8 code reduced to a 4093-bit fingerprint mask. -/
def fingerprint (g : G) : ℕ := permutationCode g.val % 4093

def mask2 : ℕ :=
  let blockBase : ℕ := 10 ^ 64
  let acc : ℕ := 1811836489610591171369950240870665185923105663197036365451043839
  let acc := acc * blockBase + 960683486462495048283750915335152417721353057619609855216784652
  let acc := acc * blockBase + 4664404133477713362416375109973761040734888629500933106592151859
  let acc := acc * blockBase + 3202771763008679185759294408838864460365040270412326943694481293
  let acc := acc * blockBase + 5567355769181553983243792866341905859337940140024329113753026599
  let acc := acc * blockBase + 5374299972124713436880043262161277633564158390065238887649738199
  let acc := acc * blockBase + 3170923142707424921461757593238087737136872232476988948783193289
  let acc := acc * blockBase + 1475475254792526523348362872886879731325122121354456679321136529
  let acc := acc * blockBase + 2507153912864890133234341435354862404137192125959963896556783368
  let acc := acc * blockBase + 7356124253645955331296693422236354947566650338809317167840498367
  let acc := acc * blockBase + 6398760118199606301197596621752855933411724625294862704162679693
  let acc := acc * blockBase + 6394665720366921954640410403330464488158552784098672468581197319
  let acc := acc * blockBase + 292518329259839316864572535459080599262173411070653854812921375
  let acc := acc * blockBase + 6132266574315341127419929768146651849543218904106272339735638244
  let acc := acc * blockBase + 6153826985079430261437919310057990017798822843718173204480346836
  let acc := acc * blockBase + 7806964368998941384974949375445013179950611394738285004653024767
  let acc := acc * blockBase + 5165162907281380838487508772773661977344240529621056526921431302
  let acc := acc * blockBase + 6386620246870854140990444190906075048081558545099992277794083456
  let acc := acc * blockBase + 491218030498587339608585329700428573478750963782724109436190720
  acc

set_option maxHeartbeats 0 in
-- Kernel evaluation checks every entry in this finite row.
theorem row2_mask : ∀ y ∈ row2, mask2.testBit (fingerprint y) = true := by
  have hcheck : row2Elements.all (fun y ↦ mask2.testBit (fingerprint y)) = true := by
    decide +kernel
  intro y hy
  change y ∈ row2Elements at hy
  exact List.all_eq_true.mp hcheck y hy

theorem row2_cover : ∀ y ∈ row2, y ≠ 1 → y ∈ row2Probes := by
  intro y hy hone
  change y ∈ row2Elements at hy
  rw [row2Elements_eq_one_cons] at hy
  exact (List.mem_cons.mp hy).resolve_left hone

/-- Rejection is deliberately conservative. -/
def rejected2 (g : G) : Bool :=
  !(fingerprintGoodCheck fingerprint mask2 row2Probes g)

def mask3 : ℕ :=
  let blockBase : ℕ := 10 ^ 64
  let acc : ℕ := 312927406797784987634493336864900415275318566831111
  let acc := acc * blockBase + 4581671734574728449643206048630031744542138324369850286439772575
  let acc := acc * blockBase + 3091384637220803139749461497216308750435646646275372855704479131
  let acc := acc * blockBase + 6999120967700998412219586249394291832585076223452941881543201398
  let acc := acc * blockBase + 6265926534844167199233535052952619935202194550734384327990710733
  let acc := acc * blockBase + 2883534763209398490076387182656423120215785130656484611316214620
  let acc := acc * blockBase + 5327951679742736783938027038110969488620117167518135454004096866
  let acc := acc * blockBase + 7852276486277519630685551917584526575661842487399113637623098250
  let acc := acc * blockBase + 5095952086869132726502871260289724255325965638943843778191199611
  let acc := acc * blockBase + 3629946068765003889799890254713277132238782650774760742919338148
  let acc := acc * blockBase + 4116185768888693463837058504247122232227646064577869007468008415
  let acc := acc * blockBase + 2680717609320959685901598008619005020598374343405449624058711529
  let acc := acc * blockBase + 9549762923683718984861595670943990311591611016055553575015141157
  let acc := acc * blockBase + 7169961113378491601810189977330927253610053898647887217546690581
  let acc := acc * blockBase + 9045060544324799256829820240936611331952929144691934982916210712
  let acc := acc * blockBase + 3513637797504967737486042084428501069840654031931380447966881414
  let acc := acc * blockBase + 9430003582312756258719428102024072403948143034345046845798792147
  let acc := acc * blockBase + 4034708541372450312838568339950761261037976305052207559840104448
  acc

set_option maxHeartbeats 0 in
-- Kernel evaluation checks every entry in this finite row.
theorem row3_mask : ∀ y ∈ row3, mask3.testBit (fingerprint y) = true := by
  have hcheck : row3Elements.all (fun y ↦ mask3.testBit (fingerprint y)) = true := by
    decide +kernel
  intro y hy
  change y ∈ row3Elements at hy
  exact List.all_eq_true.mp hcheck y hy

theorem row3_cover : ∀ y ∈ row3, y ≠ 1 → y ∈ row3Probes := by
  intro y hy hone
  change y ∈ row3Elements at hy
  rw [row3Elements_eq_one_cons] at hy
  exact (List.mem_cons.mp hy).resolve_left hone

/-- Rejection is deliberately conservative. -/
def rejected3 (g : G) : Bool :=
  !(fingerprintGoodCheck fingerprint mask3 row3Probes g)

def mask5 : ℕ :=
  let blockBase : ℕ := 10 ^ 64
  let acc : ℕ := 51492347399646214847808195087366850124375748480205
  let acc := acc * blockBase + 9675426876347750686300044075959026552817311411016919567998300028
  let acc := acc * blockBase + 8999393288161812727063176196270512571890056513454838628498566
  let acc := acc * blockBase + 41573328101289205416222360349665972000716364905595217265661269
  let acc := acc * blockBase + 2289411957462444482581168486931285882153343205094986222054829550
  let acc := acc * blockBase + 4228066409307348309558164144800431440659955213746934651882859283
  let acc := acc * blockBase + 2055179472103116257322945390922564350544195015759909189745894034
  let acc := acc * blockBase + 8032079102394547536617295707049950491825228492573700152288695571
  let acc := acc * blockBase + 7837478674000019114646404816285045894343788386868616967356082010
  let acc := acc * blockBase + 4717868514914232429253675495637899953997450938352737122914520350
  let acc := acc * blockBase + 2169763401681767533783746136666037849455196731694928675825763283
  let acc := acc * blockBase + 1233472078768303794258706387712088059450337020466807567664914502
  let acc := acc * blockBase + 2007849446991534560908865697143091476449899532588796132324389317
  let acc := acc * blockBase + 9948796520722960603968532547398957407893776908848157511573645631
  let acc := acc * blockBase + 9186117569089495894292233859080912775184461440032962152668587412
  let acc := acc * blockBase + 7861502859866954361580210733015989227151449420386635978011038925
  let acc := acc * blockBase + 3586801542916618190246249663085271776868214510543589917989451163
  let acc := acc * blockBase + 6231699549859051281984879494357105220371291791818422111425669771
  let acc := acc * blockBase + 5129952020032649646986922259054052857337995154456193174398304256
  acc

set_option maxHeartbeats 0 in
-- Kernel evaluation checks every entry in this finite row.
theorem row5_mask : ∀ y ∈ row5, mask5.testBit (fingerprint y) = true := by
  have hcheck : row5Elements.all (fun y ↦ mask5.testBit (fingerprint y)) = true := by
    decide +kernel
  intro y hy
  change y ∈ row5Elements at hy
  exact List.all_eq_true.mp hcheck y hy

theorem row5_cover : ∀ y ∈ row5, y ≠ 1 → y ∈ row5Probes := by
  intro y hy hone
  change y ∈ row5Elements at hy
  rw [row5Elements_eq_one_cons] at hy
  exact (List.mem_cons.mp hy).resolve_left hone

/-- Rejection is deliberately conservative. -/
def rejected5 (g : G) : Bool :=
  !(fingerprintGoodCheck fingerprint mask5 row5Probes g)

def mask7 : ℕ :=
  let blockBase : ℕ := 10 ^ 64
  let acc : ℕ := 5505077158783281590804124808661641027192062281814892823178781084
  let acc := acc * blockBase + 785548486053263177203491841272205626354846413027265046310058483
  let acc := acc * blockBase + 7831950655712313979867631451046290902247937871318676953494903612
  let acc := acc * blockBase + 8913354879179619531912110089627444496663881679467272605134339083
  let acc := acc * blockBase + 6446383871813046752268885511093792840521874275764057811641756162
  let acc := acc * blockBase + 9787321204981023626115622156688896127388825226867701712452869677
  let acc := acc * blockBase + 1922319045743989332666624257697670955246719680649884778748824184
  let acc := acc * blockBase + 9150387239381104494454943905655924589284863555714186253462528608
  let acc := acc * blockBase + 3355913348447685058361509141532462124887242271674460593900108515
  let acc := acc * blockBase + 2095898679472570934984956082101345657702719973531160344564689720
  let acc := acc * blockBase + 2943832046219246455921936638084950394136076082970808502720273469
  let acc := acc * blockBase + 302621930415004955174142366355227757514061642238438629940156797
  let acc := acc * blockBase + 9073774330197270300312475388723825038367152677467874245492331915
  let acc := acc * blockBase + 922491788477447396606488908969126116192527677786208472036319856
  let acc := acc * blockBase + 2358272687233036970922150553824674409320389664721957745478861889
  let acc := acc * blockBase + 4327636611639141770042802416537692477112216211558269891092095189
  let acc := acc * blockBase + 9584913283387322644693304838953028181636169237424399350855383499
  let acc := acc * blockBase + 2418502578874000661732559971517677917212183576597669797393596416
  acc

set_option maxHeartbeats 0 in
-- Kernel evaluation checks every entry in this finite row.
theorem row7_mask : ∀ y ∈ row7, mask7.testBit (fingerprint y) = true := by
  have hcheck : row7Elements.all (fun y ↦ mask7.testBit (fingerprint y)) = true := by
    decide +kernel
  intro y hy
  change y ∈ row7Elements at hy
  exact List.all_eq_true.mp hcheck y hy

theorem row7_cover : ∀ y ∈ row7, y ≠ 1 → y ∈ row7Probes := by
  intro y hy hone
  change y ∈ row7Elements at hy
  rw [row7Elements_eq_one_cons] at hy
  exact (List.mem_cons.mp hy).resolve_left hone

/-- Rejection is deliberately conservative. -/
def rejected7 (g : G) : Bool :=
  !(fingerprintGoodCheck fingerprint mask7 row7Probes g)

end LisiSabatini.FiniteCertificates.A8FingerprintData
