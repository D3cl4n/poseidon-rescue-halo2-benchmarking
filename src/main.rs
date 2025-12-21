use std::marker::PhantomData;
use ff::PrimeField;
use num_bigint::BigUint;
use std::fmt::Debug;
use std::str::FromStr;
use std::time::{Instant, Duration};
use halo2_proofs::{
    circuit::{AssignedCell, Region, Chip, Layouter, SimpleFloorPlanner, Value},
    plonk::{Advice, Fixed, Circuit, Column, ConstraintSystem, Error, Instance, Selector, Expression},
    poly::Rotation,
};

/*
* Poseidon vs. Rescue-Prime permutation benchmarking over BLS12-381
* Shared parameters: state_size = 3, rate = 2, capacity = 1, MDS, p = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001
* Poseidon specific parameters: N = 195, full_rounds = 8, partial_rounds = 57, alpha = 5
* Rescue-Prime specific parameters: rounds = 4, alpha = 3, alpha_inv = 12297829382473034371
* NOTE: Round constants also differ for both permutations, not pasted here
* NOTE: MDS matrix is the same for both permutations, not pasted here
* -------------------------------------------------------------------------------------------
* Shared Circuit Construction:
*  - 3 advice columns, one per state element
*  - 1 instance column, holding the final state values after the permutation
*  - 3 fixed columns, one per constant to be added to the state elements
*  - MDS Multiply Gate: multiplies the vector representing the state by the MDS matrix
*       - Selector: s_mds_mul
*  - Add Round Constants Gate: injects/adds 3 round constants to the state elements
*       - Selector: s_add_rcs
*  - S-Box Gate: raises the state elements to a given power
*       - Selector: s_sub_bytes
* -------------------------------------------------------------------------------------------
* Benchmarks
*  - Number of rows
*  - Number of gates enabled (also reveals number of constraints minus copy constraints)
*  - MockProver runtime
*  - Number of round constants
*  - Number of rounds
*  - Runtime for one round
*  - Advice cell count
*  - Total cell count
*  - Maximum degree
*/

// Poseidon round constants
const ROUND_CONSTANTS_PS: [&str; 195] = ["48991097081732275468845314168021420565497297775988823234113406403095118809216", "38385660029618165285848698857635215143135976511856402182142757680787979296154", "45664917788634056160947231182803089169570746657219074370482409200042991921246", "46611823467219910333349433978991031443945697128435279755908258896090196676828", "21239555800391983336673016232252577145979304597102502292785557024177155115319", "5444549814002252718699361548642546874417220826495496552290417094191494299797", "6120941817780228594851185625662354154126315032538247033968198498911791651970", "23268934541565483112488314239282439244757346303484537549209002605218913236536", "34778900561716047730386110499058136122597669775051061603711724688203374984731", "11866412958831620887953860204795878894545618212709331023611019011793447488176", "1292810553955081089139103033821163176614817808018762694232693357405135340213", "29829440149074940820671559824872937980763748927491238614065138142835318453671", "43007325278312980663982452106946226844964622384017700838855297379677047113384", "6207852559847946300667836829798951848361581084433525098597857899536657157132", "51263844854419207560514475863120683772532929850629546992690510884221364990253", "47537207485065031976374469967696134772574834313568026823983918780308518394040", "2221931791899303960239149702171682649773262449196140787838362753706579104592", "39456839086017037141295863080128693714705835125922448198802062180577619415688", "7307684192235537965831376311417883513796535701244096178785218530839409056523", "40363790847223872255995860144037894400158879326818322790255787884037990480527", "46370977865329511267956842930057959446221524060145738210680245530954549945015", "31963375456062604704511762940421329756212766442452555529101241339674782334039", "14931035994999669353073307088521670981122374648927581516990615825314462827897", "9146050314741225622437907700594105481623623087635695897868792721147700541623", "43028866523328004770172322384235815492694573248368601737155468843525625413279", "10642771813466087799681476709295362996886361934733270333728358675267521442184", "26204626472182247586446753357603232226235570940686295317661191583409532523578", "51764778305842182544341507127328333397682018984536762517144144495830254727692", "46323013798997081811959707047808149003166619133464450127989691277775183404349", "5482714761779403197336605367697000529513289823583027739458069397684408687717", "12801259943830582826718901632357112368256632783422449824889858551937326401170", "24705221370028061177410670936487461711735994635988936070623351799675117594850", "34818354068777339891091714877681898548352650337240481539567373888981659308099", "35437981511765462742605234803376772682840664204821301764084738573774616215109", "1433523918194521021731556457516832465819757187635645935518277720319249889445", "1786444825311968572352002116054188762971225383128313206702203805257523693888", "22232073076796622550494050910209988454596433174206874696362037700514082492276", "24042430109235922611027968831657325520072553641473321784508698720854180658031", "45406805567398680921065452923276055166961588153660261520529196040913487916279", "35053262861048825411061280559553895536192334830763062477277235807515959383150", "25108964803188800737437394246442073858261740146181095550988111856238954490309", "35192650141137106058577418514209092904214762437910434967540336800650620041958", "34220944794619662782589792809938215078980533657269200933482014763836254210880", "39884393792242132075258602070541114557272278571033974158755307717930033808078", "6528627567246138898338135471584665860403024864125846353758054588554049365178", "26135348890537017135058266369936506677345001674530050056494732502158573534651", "45940975099728729872716617510434185869788979733816569378448209603957649084497", "15421094974171181812057105309783852016087843260648209913425190920580878315912", "17821536801502538623431403481143359660601434134694528982404802873816360858943", "8010729838943058740614807905113741378835761166137481371357965047712306801123", "18699215163509883263304393673283276029620709331747651039747044003384506899917", "37045787943638220002917633921716309877792707850558591835874081145770158399128", "21575637935417645110089037900895429146838845113516284564671508366546944971174", "1788789771738709712587591109966362080868778924904243569200231458308784197447", "31893695366599021197812621371715665903315747385247436549810717167321695484766", "51153400179598348220410722401172031495931771158209082356586940118519763307990", "27065341612806387486757726552834268222391812301897865130062594135449450311205", "21631377794423816098233500204394685009343254816615902551641496756763638503963", "48126155452550090941025807356211843589751116110477652511672279566428926247148", "41945332685105951593851845839403181725987901258063429769257339995392450728766", "24296067579767080403247766323431204628341605710487447431323947636125286730412", "15881178462681378844988252603563609691162651204658664856493588769950563205407", "33027381395215663927148306470841421013404116814305740800948949823021554274098", "39278310473084767209787340524936392884387815060990743323143945308386189000820", "36914830105593239127583246606078015086694578878061417360363710472659792271157", "2471481831227881021689006198592503194795082772689986463565415296171852015386", "10133170919569185596470854926690039229735632740212998846069400800395437949818", "13713875128407368240685505357662717227751490836079655538057610707920043576169", "8342666644640774986634432327796294683569398370446186977217700283927741456745", "46601389125814748868096111624907238097032545985765609175268428943258314495300", "20955390743109511563797223108807741951396100480021156649651505770632943438749", "30784566406743698397200754777301033281231860349200935908047757137616877875074", "48343196439030272896030042717039190414055291776286919553358305329065060244544", "5454630884154432785537568532823077194524789618913833351503828005963129645447", "5929264687259766357446095238429932392315604113095822327000589827415320983004", "22075444908821639097706881947036304396835729534515628434816919715415538390017", "25941058816975140552446994550948593572939163972016393579803457030200129476973", "39776348414428957147819346902864822521632016599308432283712625663034427240337", "7416720880414633042939600412231360970614004283597614937824398530497243499212", "27759512177446113435859126093069895419463054324674208616122176370583357562941", "2693390255841122228782459820336527344026453452088174693463152401174043438469", "50367239350666539482528955684311280608817276753868085587890812549436189586564", "16174733649048109460569124327899128868049112853807486992529031028618670502840", "25032516686620026063532769674876936116496163673410980298313095252836905833243", "29144403930621998939944109351403497411548441156029659945515675350299265094466", "2003270776024057925128728348175382837282431082428047352264694823915738934597", "33363216671247018657387321397537436143187354110057266627888117938607035196831", "20203086474546098412356910533884833744816739556295954278635367853784856438617", "42960220771318412318176969631346524408076008158165832346168142557674200614679", "6311431299350400649257553117850994107778654765725553469026713480041524237057", "20356164198757608998824195662812920762417225019317083164408248459556033087792", "50934696509775059306730966013034554090787668615778167832259926621090584698298", "12540543785093585171832085015032615168496292565469198040103631290639480719638", "7087832377964131545651220267742883342179930832350845193376391176592931716961", "34984411233898940973869087861225504483500912780307024595154545196097892807889", "35766364158306764887416108757297765472332147961010533956614913565935878448984", "1765971701998656161486995693692800538505518481763639488010072221442068236951", "52296260704967533238281867983484652098827616020272035805695017707768629021210", "4935673489774322197628160742241883723281125866438378640636969542959380659457", "49493374663267588751846054378343301708694531580092984346087290317742537210902", "11234520985865325412206403291118519753189986845681526796638090446788348697652", "24240566602759984788029880030276085623682320979885122363103446030346976862554", "45173673056688650486124798353267048676515652881324846851443098010775612892322", "273339079894952168974065527137723282564095652951909656957160946114792896627", "4470325051640351957976738782642661997153601739638632363210829100051811744274", "35146154431885107533179241729875580217482204780231937987130147605583867466092", "5623976303155942456710618286519758761204923686926813378548021075733755166889", "24016465951530015578209275233668961482322584131459513288081598210134015257997", "17969920097176891022415687639709999939084490545645205326481661860931808113029", "45152206508674411747856285000257938228137174933577379726580072509850619926251", "38945634795250927360607537392732805897873100986379288027606175928019977509609", "32851666289693613044889283133849490343674968726730793059165429991055922454070", "31944620853700630151347751910587969550223781655480776781612692884058563662268", "25256966274452535017610572446887439115046074651331211781708168773655007778872", "9486939021502590608732001628331695421223550406038486802197261945175668785507", "39459143086960362426927505137137876218390935544236059938922871880000296175208", "31894450224048346260322339655447950546670422421242715439734122749915296243605", "26892539091318428420931225040417651442139701587930804697886023619431558542747", "2542844944718735302766446637202404427628413878092734865912744553984157161261", "31883859221346313107414474846252752604992097590133961842848913019073014153010", "51303361359653464050006771537341226976539604964205923399469614564706008834052", "51171387502764330562774849667033034283056080450385872897204773223645085369254", "7237091576916241695047293084522141336268656276386088021954481852199921973216", "25026554458962841467968682601680143746537618788336396538569095145280445662154", "16003513886762983460717836271035484656754723355114772159990269505739759600774", "20742179979178809796122395691368538694837598010689782796398715701486525085958", "44785832974715571208383539748048195425158621451201620091409304675643540484444", "40997683756979855969631370242290487603852436449608298499325558394715696204831", "24039577999618876159836452559464600377553684696598310542830185648570694947325", "214991500380221402745874275507138825943309188151683861156767017258335759518", "37648944229324812379904445632193391903358473357814505256571234492472677352375", "33262001091080721927187326829375441597312853742311915461357184164050334176171", "12889759088432190033171086881844675377815686311282488955569491035800531227592", "38889970121432469903433846063190552781925277874128916432889442865031400486457", "9686759546395317438502700818478291413888291261781927399197594299119600593872", "25228839869827315437841994432860023863461613471517457235105091951188556007171", "29251067411858749210993269168637503659802522399342640488863629751155422442084", "40912660681512278236165911366927220401330409827994264103091984300131586078341", "12796501909444494709088656380507035418412240267936921974592450125220369752821", "41489997591227135571666436387925119767986380278590920811343183082128452793080", "21497862265009693334292006570547451455021214638930393134366176167326805799325", "42759488993366187559528022270353477068325476435317366129099617149236057994173", "51812786435352958751631482409057671996557140765865434087196139886155873550638", "49668984917578993057336571483567900930503120626539459296975328351727319861276", "16647828498038646540925328826301561929374469486623027976723819473821480409681", "48148303340548214354795067112758174231010308760482898449349672592745234924387", "40514099213939369482769058963482609316155051560990264349668700968914554718236", "36567947302783543506732234132138195442155777559454242003814702099955749246290", "22396816925035795192842094319757131771178499933587237012855640944068186589937", "47761479716265566311036142819261705369735044145214592608213591050556455450430", "13277094590686127307617107451297268367321013828763858520220510028318248040673", "6273610774394348396010704017556554992266752629801490457323912355626787108751", "47394279615623798760617602748864924711531390489909756029248999925570450315302", "27952252793623580780344613559829677253211432925530630621608481053048520434744", "1683222943011658234228486862639342402730538635204883039431226239924268835592", "6849709550515639669397513895396396226183305237153796793058311861850242817732", "51524350017816629912679960748295545024593637560633508281874724597080573807830", "26590614177194547630006347843068513496427790322854759433492355517360208924714", "31548830001396651725711310298465958490865636855427227043617585502978053092924", "14291568473806392803367440164088272381690062239638560607879858528716058147676", "21146452903160991922099734199583866923318964586815062550024895407430164358523", "22961005724583382013438450487662047962072123198815308647967555251332825175693", "4752908842318626074338926279870993084957055641402767877988223199262408017438", "41544523600430331260332604149473035199994864893327747257504064038791086157408", "17323878296591859990733132832893641096022161936583121997952997880406237212813", "18014582744613086697405046476881081314871698927785490238333612330034405321202", "45325447140824171211209633262297712878556500592023247082629492785769121758434", "6192753434333002929210820794040779560623421075700800400752599138519650269040", "12937001546279985738495952624875312380127801527837660882855310431015537184413", "45991618799696924909840068913271150748052998998510820293768267349781597832497", "37441188106719457933929221474454571110916912448355945524409576665808556247872", "49875923679586708113406579244909793162425404239213510953269412337363307325571", "15051465698071304017966667797323113094420513709580063806706433232853573089040", "10338905189138871748742400929101717755982978259187828256039071250817040249017", "40261933448177008341539991920645739011692467645144896682394869561245899318641", "38346498339252184147870281431364733631809877281747451440216067081256241485418", "6209216396715641040468803949857167055175110420218294975303260728579180870134", "25923422290512595808420551575642237631007497169886590851128840338102194873726", "11953618934086915505672657493115697182858104796786340137294500949047339928290", "48506710952023206646326838201389789459004051035511888474426942257560405427104", "49584811575438811511092715559885015474424100729555178730940640525393341823572", "25222528947373923151054372702664425173210441980263130389325557963853429239320", "36212452941316997504575803214309342413443151488267891949906815090453746563323", "19548334171603533109137618032918088438321356008712800140019849908969476369140", "13369714008256347363334888026585995433724817786797528430136744458743428376798", "23153174875441426069922538845839074574095797738892298576581895020444392853731", "19950632315767750645780485212179021291844439659606854957365124208057044477001", "4990085320684307481424051057758258811192003289472239932032551966513564492664", "29810043862384409261569733347989054089853302964778668946432779952952625186706", "10937492441648375945337911315608624372433158520395209903090712138844575570844", "24981706249730491732129119057314109520549309496394969130105355950186024721860", "10498082524469215029826843019306692952360905490979497919767209022386939911216", "15682375221169428458922809183562392617423770660027773228464622792081026981791", "41914385147673242564111169184735297479310144571630342213035237856939024640011", "39667818743665708661866396692813914317148400284941420155363896112617842800421"];

// Rescue-Prime round constants
const ROUND_CONSTANTS_RS: [[&str; 3]; 8] = [["41550313466542986686381187475386224890619213663365144133966235154580769474314", "46235636976106534322257334778843335414724041131494488188341064387240106153243", "43314474564749977258448857367299700960955407362432105710780024592683745356396"], ["6610248367712747417489710323792672924291015441980260828503764505802544302133", "48902835969048727949157312845529356609975996102724786706493615060533278826882", "48020430798213331714265136872960067665339968785807617895912965210318833506033"], ["46852092121783048129054015209292285454336628007814272371588179933784556551027", "18285529991400289460558442082097384209909111358722088777170630517004445042401", "39715240121717033403976206014745165566831987912684275661267961794798544871325"], ["39129494641659579693129270149028838267319001600817760345550310657253464282481", "16498478026547012198311182730134271651465725575734990928064879994773584955147", "15538063473797736748725276996847281947218186074842698727649618962576399148406"], ["12101073411609416127490814861966272020523587207284114445457770741397044122169", "41191457238696909629534734120094776042526534898929749767454246268859687595206", "14461612708761797000547489494258040283490469843669982750248191854462915994269"], ["21457542915987289663022414331227578968074137299214232740648201393058262727787", "29910968875453454114258285197546306058264337380169261403677155868116380953177", "1898093979887951345662468894551151764048081657277492505601547831464044030732"], ["48489871713406609021659256694551631688695628741735467423625834725439773239420", "15812043658450185541651447416198363552300888092238882774860191251166424574103", "25192733271269000031278313438764703304293505356764019300933833584278095057211"], ["51449973959999043781013692277642864865788635636442612709446611274677398875715", "7335113001153546988973758758642349543575276014251270978519899059245031076651", "38071662158091447967518913580232801247205163003871086365540004964717937594515"]];
// structure to store numbers in cells
struct Number<F: PrimeField>(AssignedCell<F, F>);

// structure for shared parameters for permutation functions
#[derive(Clone, Debug)]
struct PermutationParameters<F: PrimeField> {
    state_size: usize,
    rate: usize,
    capacity: usize,
    mds: [[F; 3]; 3] 
}

// structure for Poseidon specific permutation parameters
#[derive(Clone, Debug)]
struct Poseidon<F: PrimeField> {
    common_params: PermutationParameters<F>,
    partial_rounds: usize,
    full_rounds: usize,
    n: usize,
    alpha: F
}

// structure for Rescue-Prime specific permutation parameters
#[derive(Clone, Debug)]
struct RescuePrime<F: PrimeField> {
    common_params: PermutationParameters<F>,
    rounds: usize,
    alpha: F,
    alpha_inv: BigUint
}

// struture for common circuit parameters
#[derive(Clone, Debug)]
struct CircuitParameters {
    advice: [Column<Advice>; 3],
    fixed: [Column<Fixed>; 3],
    instance: Column<Instance>,
    s_mds_mul: Selector,
    s_add_rcs: Selector
}

// Poseidon chip configuration
#[derive(Clone, Debug)]
struct PoseidonChipConfig<F: PrimeField> {
    permutation_params: Poseidon<F>,
    circuit_params: CircuitParameters,
    _marker: PhantomData<F>,
    // the below selectors are specific to Poseidon (Hades construction)
    s_sub_bytes_full: Selector,
    s_sub_bytes_partial: Selector
}

// Rescue-Prime chip configuration
#[derive(Clone, Debug)]
struct RescueChipConfig<F: PrimeField> {
    permutation_params: RescuePrime<F>,
    circuit_params: CircuitParameters,
    _marker: PhantomData<F>,
    // the selector below is specific to Rescue-Prime
    s_sub_bytes: Selector,
    s_sub_bytes_inv: Selector
}

// structure for the poseidon permutation chip
struct PoseidonChip<F: PrimeField> {
    config: PoseidonChipConfig<F>,
    _marker: PhantomData<F>,
}

// structure for the poseidon permutation chip
struct RescueChip<F: PrimeField> {
    config: RescueChipConfig<F>,
    _marker: PhantomData<F>,
}

// Poseidon circuit structure TODO: is this worth abstraction if I need two synthesizing calls anyways?
#[derive(Default)]
struct PoseidonCircuit<F: PrimeField> {
    s0: Value<F>, 
    s1: Value<F>, 
    s2: Value<F>
}

// Rescue-Prime circuit structure
#[derive(Default)]
struct RescueCircuit<F: PrimeField> {
    s0: Value<F>, 
    s1: Value<F>, 
    s2: Value<F>
}

// implement the Chip trait for PoseidonChip
impl<F: PrimeField> Chip<F> for PoseidonChip<F> {
    type Config = PoseidonChipConfig<F>;
    type Loaded = ();

    // getter for the chip config
    fn config(&self) -> &Self::Config {
        &self.config
    }

    // getter for the loaded field
    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

// implement the Chip trait for RescueChip
impl<F: PrimeField> Chip<F> for RescueChip<F> {
    type Config = RescueChipConfig<F>;
    type Loaded = ();

    // getter for the chip config
    fn config(&self) -> &Self::Config {
        &self.config
    }

    // getter for the loaded field
    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

// helper methods that both chips call when configuring (gate construction, column configurations, etc.)
// gates created are stored in the ConstraintSystem instance
fn create_arc_gate<F: PrimeField>(
    meta: &mut ConstraintSystem<F>, 
    advice: [Column<Advice>; 3], 
    fixed: [Column<Fixed>; 3], 
    s_add_rcs: Selector
) {
    meta.create_gate("ARC_Gate", |meta| {
        let s_add_rcs = meta.query_selector(s_add_rcs);
        let a0 = meta.query_advice(advice[0], Rotation::cur());
        let a1 = meta.query_advice(advice[1], Rotation::cur());
        let a2 = meta.query_advice(advice[2], Rotation::cur());
        let a0_next = meta.query_advice(advice[0], Rotation::next());
        let a1_next = meta.query_advice(advice[1], Rotation::next());
        let a2_next = meta.query_advice(advice[2], Rotation::next());
        let rc0 = meta.query_fixed(fixed[0]); // query_fixed reads from current row when gate is active
        let rc1 = meta.query_fixed(fixed[1]);
        let rc2 = meta.query_fixed(fixed[2]);

        // constraint should be vec![0, 0, 0]
        vec![
            s_add_rcs.clone() * (a0_next - (a0 + rc0)), 
            s_add_rcs.clone() * (a1_next - (a1 + rc1)), 
            s_add_rcs * (a2_next - (a2 + rc2))
        ]
    });
}

fn create_mds_mul_gate<F: PrimeField>(
    meta: &mut ConstraintSystem<F>, 
    advice: [Column<Advice>; 3], 
    s_mds_mul: Selector,
    mds: &[[F; 3]; 3]
) {
    meta.create_gate("ML_gate", |meta| {
        let s_mds_mul = meta.query_selector(s_mds_mul);
        let a0 = meta.query_advice(advice[0], Rotation::cur());
        let a1 = meta.query_advice(advice[1], Rotation::cur());
        let a2 = meta.query_advice(advice[2], Rotation::cur());
        let a0_next = meta.query_advice(advice[0], Rotation::next());
        let a1_next = meta.query_advice(advice[1], Rotation::next());
        let a2_next = meta.query_advice(advice[2], Rotation::next());

        // MDS matrix elements from row in column 0 -> column 2 order, use Expression:Constant to embed into polynomial
        let mds_0_0 = Expression::Constant(mds[0][0]);
        let mds_0_1 = Expression::Constant(mds[0][1]);
        let mds_0_2 = Expression::Constant(mds[0][2]);
        let mds_1_0 = Expression::Constant(mds[1][0]);
        let mds_1_1 = Expression::Constant(mds[1][1]);
        let mds_1_2 = Expression::Constant(mds[1][2]);
        let mds_2_0 = Expression::Constant(mds[2][0]);
        let mds_2_1 = Expression::Constant(mds[2][1]);
        let mds_2_2 = Expression::Constant(mds[2][2]);
        
        // constraint - computes vector matrix product
        vec![
            s_mds_mul.clone() * (a0_next - (a0.clone()*mds_0_0 + a1.clone()*mds_0_1 + a2.clone()*mds_0_2)),
            s_mds_mul.clone() * (a1_next - (a0.clone()*mds_1_0 + a1.clone()*mds_1_1 + a2.clone()*mds_1_2)),
            s_mds_mul * (a2_next - (a0*mds_2_0 + a1*mds_2_1 + a2*mds_2_2))
        ]
    });
}

// helper functions for creating Poseidon specific gates
fn create_partial_sbox_gate_ps<F: PrimeField>(
    meta: &mut ConstraintSystem<F>,
    advice: Column<Advice>,
    s_sub_bytes_partial: Selector, 
) {
    meta.create_gate("PS_partial_sbox_gate", |meta| {
        let s_sub_bytes_partial = meta.query_selector(s_sub_bytes_partial);
        let a0 = meta.query_advice(advice, Rotation::cur()); // state[0] = state[0]**5, alpha = 5
        let a0_next = meta.query_advice(advice, Rotation::next());

        vec![s_sub_bytes_partial* (a0_next - (a0.clone()*a0.clone()*a0.clone()*a0.clone()*a0))]
    });
}

fn create_full_sbox_gate_ps<F: PrimeField>(
    meta: &mut ConstraintSystem<F>,
    advice: [Column<Advice>; 3],
    s_sub_bytes_full: Selector, 
) {
    meta.create_gate("PS_full_sbox_gate", |meta| {
        let s_sub_bytes_full = meta.query_selector(s_sub_bytes_full);
        let a0 = meta.query_advice(advice[0], Rotation::cur());
        let a1 = meta.query_advice(advice[1], Rotation::cur());
        let a2 = meta.query_advice(advice[2], Rotation::cur()); 
        let a0_next = meta.query_advice(advice[0], Rotation::next());
        let a1_next = meta.query_advice(advice[1], Rotation::next());
        let a2_next = meta.query_advice(advice[2], Rotation::next()); 

        vec![
            s_sub_bytes_full.clone() * (a0_next - (a0.clone()*a0.clone()*a0.clone()*a0.clone()*a0)),
            s_sub_bytes_full.clone() * (a1_next - (a1.clone()*a1.clone()*a1.clone()*a1.clone()*a1)),
            s_sub_bytes_full * (a2_next - (a2.clone()*a2.clone()*a2.clone()*a2.clone()*a2))
        ]
    });
}

// helper functions for creating Rescue-Prime specific gates
// alpha = 5
// alpha_inv = 20974350070050476191779096203274386335076221000211055129041463479975432473805 = inverse(5, p-1)
fn create_sbox_gate_rs<F: PrimeField>(
    meta: &mut ConstraintSystem<F>, 
    advice: [Column<Advice>; 3],
    s_sub_bytes: Selector
) {
    meta.create_gate("RS_sbox_gate", |meta| {
        let s_sub_bytes = meta.query_selector(s_sub_bytes);
        let a0 = meta.query_advice(advice[0], Rotation::cur());
        let a1 = meta.query_advice(advice[1], Rotation::cur());
        let a2 = meta.query_advice(advice[2], Rotation::cur()); 
        let a0_next = meta.query_advice(advice[0], Rotation::next());
        let a1_next = meta.query_advice(advice[1], Rotation::next());
        let a2_next = meta.query_advice(advice[2], Rotation::next());

        vec![
            s_sub_bytes.clone() * (a0_next - (a0.clone()*a0.clone()*a0.clone()*a0.clone()*a0)),
            s_sub_bytes.clone() * (a1_next - (a1.clone()*a1.clone()*a1.clone()*a1.clone()*a1)),
            s_sub_bytes * (a2_next - (a2.clone()*a2.clone()*a2.clone()*a2.clone()*a2))
        ]
    });
}

fn create_sbox_inv_gate_rs<F: PrimeField>(
    meta: &mut ConstraintSystem<F>,
    advice: [Column<Advice>; 3],
    s_sub_bytes_inv: Selector
) {
    meta.create_gate("RS_sbox_inv_gate", |meta| {
        let s_sub_bytes_inv = meta.query_selector(s_sub_bytes_inv);
        let a0 = meta.query_advice(advice[0], Rotation::cur());
        let a1 = meta.query_advice(advice[1], Rotation::cur());
        let a2 = meta.query_advice(advice[2], Rotation::cur()); 
        let a0_next = meta.query_advice(advice[0], Rotation::next());
        let a1_next = meta.query_advice(advice[1], Rotation::next());
        let a2_next = meta.query_advice(advice[2], Rotation::next());

        // constrain a_next^alpha = a_current instead of a_next = a_current^alpha_inv
        vec![
            s_sub_bytes_inv.clone() * (a0 - (a0_next.clone()*a0_next.clone()*a0_next.clone()*a0_next.clone()*a0_next)),
            s_sub_bytes_inv.clone() * (a1 - (a1_next.clone()*a1_next.clone()*a1_next.clone()*a1_next.clone()*a1_next)),
            s_sub_bytes_inv * (a2 - (a2_next.clone()*a2_next.clone()*a2_next.clone()*a2_next.clone()*a2_next))
        ]
    });
}

// implementation of additional methods for the PoseidonChip
impl<F: PrimeField> PoseidonChip<F> {
    // constructor
    fn construct(config: <Self as Chip<F>>::Config) -> Self {
        PoseidonChip { config, _marker: PhantomData}
    }

    // configure the chip including all gates, constraints, and selectors
    fn configure(
        meta: &mut ConstraintSystem<F>,
        advice: [Column<Advice>; 3],
        fixed: [Column<Fixed>; 3],
        instance: Column<Instance>,
        params: Poseidon<F>
    ) -> <Self as Chip<F>>::Config {
        // enable equality constraints on the instance column
        meta.enable_equality(instance);

        // enable equality constraits on all advice columns
        for column in &advice {
            meta.enable_equality(*column);
        }

        // enable constant on all the fixed columns
        for column in &fixed {
            meta.enable_constant(*column);
        }

        let s_add_rcs = meta.selector();
        let s_mds_mul = meta.selector();
        let s_sub_bytes_full = meta.selector();
        let s_sub_bytes_partial = meta.selector();  

        // create gates and constraints
        create_arc_gate(meta, advice, fixed, s_add_rcs);
        create_mds_mul_gate(meta, advice, s_mds_mul, &params.common_params.mds);
        create_full_sbox_gate_ps(meta, advice, s_sub_bytes_full);
        create_partial_sbox_gate_ps(meta, advice[0], s_sub_bytes_partial);

        let circuit_params = CircuitParameters {
            advice,
            fixed,
            instance,
            s_mds_mul,
            s_add_rcs
        };
        
        // return the config
        PoseidonChipConfig {
            permutation_params: params,
            circuit_params,
            _marker: PhantomData,
            s_sub_bytes_full,
            s_sub_bytes_partial
        }
    }
}

// implementation of additional methods for the RescueChip
impl<F: PrimeField> RescueChip<F> {
    // constructor
    fn construct(config: <Self as Chip<F>>::Config) -> Self {
        RescueChip { config, _marker: PhantomData}
    }

    // configure the chip including all gates, constraints, and selectors
    fn configure(
        meta: &mut ConstraintSystem<F>,
        advice: [Column<Advice>; 3],
        fixed: [Column<Fixed>; 3],
        instance: Column<Instance>,
        params: RescuePrime<F>
    ) -> <Self as Chip<F>>::Config {
        // enable equality constraints on the instance column
        meta.enable_equality(instance);

        // enable equality constraits on all advice columns
        for column in &advice {
            meta.enable_equality(*column);
        }

        // enable constant on all the fixed columns
        for column in &fixed {
            meta.enable_constant(*column);
        }

        let s_add_rcs = meta.selector();
        let s_mds_mul = meta.selector();
        let s_sub_bytes = meta.selector();
        let s_sub_bytes_inv = meta.selector();  

        // create gates and constraints
        create_arc_gate(meta, advice, fixed, s_add_rcs);
        create_mds_mul_gate(meta, advice, s_mds_mul, &params.common_params.mds);
        create_sbox_gate_rs(meta, advice, s_sub_bytes);
        create_sbox_inv_gate_rs(meta, advice, s_sub_bytes_inv);

        let circuit_params = CircuitParameters {
            advice,
            fixed,
            instance,
            s_mds_mul,
            s_add_rcs
        };
        
        // return the config
        RescueChipConfig {
            permutation_params: params,
            circuit_params,
            _marker: PhantomData,
            s_sub_bytes,
            s_sub_bytes_inv
        }
    }
}

// trait for the sub-functions of the circuit
trait PermutationInstructions<F: PrimeField>: Chip<F> {
    type Num;

    // expose a value as public for
    fn expose_as_public(&self, layouter: impl Layouter<F>, num: Self::Num, row: usize) -> Result<(), Error>;

    // permutation
    fn permute(
        &self, 
        layouter: impl Layouter<F>,
        a0: Value<F>,
        a1: Value<F>,
        a2: Value<F>
    ) -> Result<[Self::Num; 3], Error>;
}

// implementation of the PermutationInstructions trait for the PoseidonChip
impl<F: PrimeField> PermutationInstructions<F> for PoseidonChip<F> {
    type Num = Number<F>;

    fn expose_as_public(&self, mut layouter: impl Layouter<F>, num: Self::Num, row: usize) -> Result<(), Error> {
        let config = self.config();
        layouter.constrain_instance(num.0.cell(), config.circuit_params.instance, row)
    }

    fn permute(
        &self, mut layouter: impl Layouter<F>, 
        a0: Value<F>,
        a1: Value<F>,
        a2: Value<F>
    ) -> Result<[Self::Num; 3], Error> {
        let config = self.config();
        layouter.assign_region(
            || "Poseidon_Permutation", |mut region| {
                let mut constant_idx: usize = 0; // index into round constants
                let mut offset: usize = 0; // row index for computations on state

                // initial state
                let mut state = [
                    region.assign_advice(|| "state_0", config.circuit_params.advice[0], offset, || a0)?,
                    region.assign_advice(|| "state_1", config.circuit_params.advice[1], offset, || a1)?, 
                    region.assign_advice(|| "state_2", config.circuit_params.advice[2], offset, || a2)?
                ];

                // helper function for power of 5 for SubBytes (in-place modification)
                let pow5 = |a: F| -> F {
                    let temp = a * a; // a^2
                    let temp_1 = temp * temp; // a^4
                    a * temp_1 // a^5
                };

                // helper function for computing one poseidon round full or partial based on boolean
                let poseidon_round = |
                    region: &mut Region<F>,
                    state: &mut [AssignedCell<F, F>; 3],
                    constant_idx: &mut usize,
                    offset: &mut usize,
                    full_round: bool
                | -> Result<(), Error> {
                    // assign the needed round constants to the fixed column for gate to read from, use local vars for state
                    let rc0 = F::from_str_vartime(ROUND_CONSTANTS_PS[*constant_idx]).unwrap();
                    let rc1 = F::from_str_vartime(ROUND_CONSTANTS_PS[*constant_idx + 1]).unwrap();
                    let rc2 = F::from_str_vartime(ROUND_CONSTANTS_PS[*constant_idx + 2]).unwrap();
                    region.assign_fixed(|| "c0", config.circuit_params.fixed[0], *offset, || Value::known(rc0))?;
                    region.assign_fixed(|| "c1", config.circuit_params.fixed[1], *offset, || Value::known(rc1))?;
                    region.assign_fixed(|| "c2", config.circuit_params.fixed[2], *offset, || Value::known(rc2))?;

                    config.circuit_params.s_add_rcs.enable(region, *offset)?; // enable the ARC selector 
                    *constant_idx += 3; // 3 round constants used from the flat list
                    *offset += 1; // first row used for fixed columns and initial state

                    let after_arc = [
                        state[0].value().map(|v| *v + rc0),
                        state[1].value().map(|v| *v + rc1),
                        state[2].value().map(|v| *v + rc2)
                    ];

                    // assign state values after ARC to advice columns
                    state[0] = region.assign_advice(|| "s0_arc", config.circuit_params.advice[0], *offset, || after_arc[0])?;
                    state[1] = region.assign_advice(|| "s1_arc", config.circuit_params.advice[1], *offset, || after_arc[1])?;
                    state[2] = region.assign_advice(|| "s2_arc", config.circuit_params.advice[2], *offset, || after_arc[2])?;

                    // SubBytes based on parameter for full or partial round (partial round only applies to state[0])
                    if full_round == true {
                        config.s_sub_bytes_full.enable(region, *offset)?;
                        *offset += 1;

                        let after_sb = [
                            state[0].value().map(|v| pow5(*v)),
                            state[1].value().map(|v| pow5(*v)),
                            state[2].value().map(|v| pow5(*v))
                        ];

                        state[0] = region.assign_advice(|| "s0_sb", config.circuit_params.advice[0], *offset, || after_sb[0])?;
                        state[1] = region.assign_advice(|| "s1_sb", config.circuit_params.advice[1], *offset, || after_sb[1])?;
                        state[2] = region.assign_advice(|| "s2_sb", config.circuit_params.advice[2], *offset, || after_sb[2])?;
                    }

                    else {
                        config.s_sub_bytes_partial.enable(region, *offset)?;
                        *offset += 1;
                        state[0] = region.assign_advice(|| "s0_sb", config.circuit_params.advice[0], *offset, || state[0].value().map(|v| pow5(*v)))?;
                        // copy other values to new offset, without modification
                        region.assign_advice(|| "s1_sb", config.circuit_params.advice[1], *offset, || state[1].value().copied())?;
                        region.assign_advice(|| "s1_sb", config.circuit_params.advice[2], *offset, || state[2].value().copied())?;
                    }

                    // MixLayer
                    config.circuit_params.s_mds_mul.enable(region, *offset)?;
                    *offset += 1;
                    
                    let mds = [
                        [
                            config.permutation_params.common_params.mds[0][0], 
                            config.permutation_params.common_params.mds[0][1], 
                            config.permutation_params.common_params.mds[0][2]],
                        [
                            config.permutation_params.common_params.mds[1][0], 
                            config.permutation_params.common_params.mds[1][1], 
                            config.permutation_params.common_params.mds[1][2]
                        ],
                        [
                            config.permutation_params.common_params.mds[2][0], 
                            config.permutation_params.common_params.mds[2][1], 
                            config.permutation_params.common_params.mds[2][2]
                        ]
                    ];

                    // extract copies of state values using .value().copied() then nest map() calls to get inner values
                    let after_ml = [
                        state[0].value().copied()
                            .zip(state[1].value().copied())
                            .zip(state[2].value().copied()) // gives ((Value<F>, Value<F>), Value<F>)
                            .map(|((s0, s1), s2)| {
                                s0 * mds[0][0] + s1 * mds[0][1] + s2 * mds[0][2]
                            }),
                        state[0].value().copied()
                            .zip(state[1].value().copied())
                            .zip(state[2].value().copied())
                            .map(|((s0, s1), s2)| {
                                s0 * mds[1][0] + s1 * mds[1][1] + s2 * mds[1][2]
                            }),
                        state[0].value().copied()
                            .zip(state[1].value().copied())
                            .zip(state[2].value().copied()) 
                            .map(|((s0, s1), s2)| {
                                s0 * mds[2][0] + s1 * mds[2][1] + s2 * mds[2][2]
                            }),
                    ];

                    state[0] = region.assign_advice(|| "s0_ml", config.circuit_params.advice[0], *offset, || after_ml[0])?;
                    state[1] = region.assign_advice(|| "s1_ml", config.circuit_params.advice[1], *offset, || after_ml[1])?;
                    state[2] = region.assign_advice(|| "s2_ml", config.circuit_params.advice[2], *offset, || after_ml[2])?;

                    Ok(())
                };

                // half of the full rounds
                for _ in 0..(config.permutation_params.full_rounds / 2) { 
                    poseidon_round(&mut region, &mut state, &mut constant_idx, &mut offset, true)?;
                }

                // all of the partial rounds
                for _ in 0..config.permutation_params.partial_rounds {
                    poseidon_round(&mut region, &mut state, &mut constant_idx, &mut offset, false)?;
                }

                // second half of the full rounds
                for _ in 0..(config.permutation_params.full_rounds / 2) {
                    poseidon_round(&mut region, &mut state, &mut constant_idx, &mut offset, true)?;
                }

                Ok([Number(state[0].clone()), Number(state[1].clone()), Number(state[2].clone())])
            }
        )
    }
}

// implementation of the PermutationInstructions trait for the RescueChip
impl<F: PrimeField> PermutationInstructions<F> for RescueChip<F> {
    type Num = Number<F>;

    fn expose_as_public(&self, mut layouter: impl Layouter<F>, num: Self::Num, row: usize) -> Result<(), Error> {
        let config = self.config();
        layouter.constrain_instance(num.0.cell(), config.circuit_params.instance, row)
    }

    fn permute(
        &self, mut layouter: impl Layouter<F>, 
        a0: Value<F>,
        a1: Value<F>,
        a2: Value<F>
    ) -> Result<[Self::Num; 3], Error> {
        let config = self.config();
        layouter.assign_region(
            || "Rescue-Prime_Permutation", |mut region| {
                let mut offset: usize = 0; // row index for computations on state

                // initial state
                let mut state = [
                    region.assign_advice(|| "state_0", config.circuit_params.advice[0], offset, || a0)?,
                    region.assign_advice(|| "state_1", config.circuit_params.advice[1], offset, || a1)?, 
                    region.assign_advice(|| "state_2", config.circuit_params.advice[2], offset, || a2)?
                ];

                // helper function for power of 5 for SubBytes (in-place modification)
                let pow5 = |a: F| -> F {
                    let temp = a * a; // a^2
                    let temp_1 = temp * temp; // a^4
                    a * temp_1 // a^5
                };

                // helper function for MDS multiplication
                let mds_mul = |
                    state: &mut [AssignedCell<F, F>; 3], region: &mut Region<F>, offset: &mut usize
                | -> Result<(), Error> {
                    let mds = [
                        [
                            config.permutation_params.common_params.mds[0][0], 
                            config.permutation_params.common_params.mds[0][1], 
                            config.permutation_params.common_params.mds[0][2]
                        ],
                        [
                            config.permutation_params.common_params.mds[1][0], 
                            config.permutation_params.common_params.mds[1][1], 
                            config.permutation_params.common_params.mds[1][2]
                        ],
                        [
                            config.permutation_params.common_params.mds[2][0], 
                            config.permutation_params.common_params.mds[2][1], 
                            config.permutation_params.common_params.mds[2][2]
                        ]
                    ];

                    config.circuit_params.s_mds_mul.enable(region, *offset)?;
                    *offset += 1;

                    let after_ml = [
                        state[0].value().copied()
                            .zip(state[1].value().copied())
                            .zip(state[2].value().copied()) // gives ((Value<F>, Value<F>), Value<F>)
                            .map(|((s0, s1), s2)| {
                                s0 * mds[0][0] + s1 * mds[0][1] + s2 * mds[0][2]
                            }),
                        state[0].value().copied()
                            .zip(state[1].value().copied())
                            .zip(state[2].value().copied())
                            .map(|((s0, s1), s2)| {
                                s0 * mds[1][0] + s1 * mds[1][1] + s2 * mds[1][2]
                            }),
                        state[0].value().copied()
                            .zip(state[1].value().copied())
                            .zip(state[2].value().copied()) 
                            .map(|((s0, s1), s2)| {
                                s0 * mds[2][0] + s1 * mds[2][1] + s2 * mds[2][2]
                            }),
                    ];

                    state[0] = region.assign_advice(|| "s0_ml", config.circuit_params.advice[0], *offset, || after_ml[0])?;
                    state[1] = region.assign_advice(|| "s1_ml", config.circuit_params.advice[1], *offset, || after_ml[1])?;
                    state[2] = region.assign_advice(|| "s2_ml", config.circuit_params.advice[2], *offset, || after_ml[2])?;

                    Ok(())
                };

                // helper function for injecting the round constants
                let inject_rcs = |
                    state: &mut [AssignedCell<F, F>; 3], 
                    region: &mut Region<F>, 
                    offset: &mut usize, 
                    idx: usize,
                | -> Result<(), Error> {
                    // assign the needed round constants to the fixed column for gate to read from, use local vars for state
                    let rc0 = F::from_str_vartime(ROUND_CONSTANTS_RS[idx][0]).unwrap();
                    let rc1 = F::from_str_vartime(ROUND_CONSTANTS_RS[idx][1]).unwrap();
                    let rc2 = F::from_str_vartime(ROUND_CONSTANTS_RS[idx][2]).unwrap();
                    region.assign_fixed(|| "c0", config.circuit_params.fixed[0], *offset, || Value::known(rc0))?;
                    region.assign_fixed(|| "c1", config.circuit_params.fixed[1], *offset, || Value::known(rc1))?;
                    region.assign_fixed(|| "c2", config.circuit_params.fixed[2], *offset, || Value::known(rc2))?;

                    config.circuit_params.s_add_rcs.enable(region, *offset)?; // enable the ARC selector 
                    *offset += 1; 

                    let after_arc = [
                        state[0].value().map(|v| *v + rc0),
                        state[1].value().map(|v| *v + rc1),
                        state[2].value().map(|v| *v + rc2)
                    ];

                    state[0] = region.assign_advice(|| "s0_sb", config.circuit_params.advice[0], *offset, || after_arc[0])?;
                    state[1] = region.assign_advice(|| "s1_sb", config.circuit_params.advice[1], *offset, || after_arc[1])?;
                    state[2] = region.assign_advice(|| "s2_sb", config.circuit_params.advice[2], *offset, || after_arc[2])?;

                    Ok(())
                };

                // helper function for computing one rescue round
                let rescue_round = |
                    region: &mut Region<F>,
                    state: &mut [AssignedCell<F, F>; 3],
                    round: usize,
                    offset: &mut usize,
                | -> Result<(), Error> {
                    config.s_sub_bytes.enable(region, *offset)?;
                    *offset += 1;

                    let after_sb = [
                        state[0].value().map(|v| pow5(*v)),
                        state[1].value().map(|v| pow5(*v)),
                        state[2].value().map(|v| pow5(*v))
                    ];

                    state[0] = region.assign_advice(|| "s0_sb", config.circuit_params.advice[0], *offset, || after_sb[0])?;
                    state[1] = region.assign_advice(|| "s1_sb", config.circuit_params.advice[1], *offset, || after_sb[1])?;
                    state[2] = region.assign_advice(|| "s2_sb", config.circuit_params.advice[2], *offset, || after_sb[2])?;

                    // MDS Multiplication helper function
                    mds_mul(state, region, offset)?;

                    // Add/Inject Round Constants helper function
                    inject_rcs(state, region, offset, 2*round)?;
                    
                    // inverse SubBytes
                    config.s_sub_bytes_inv.enable(region, *offset)?;
                    *offset += 1;
                    
                    let alpha_inv_vec: Vec<u64> = config.permutation_params.alpha_inv.to_u64_digits();

                    let after_sb_inv = [
                        state[0].value().map(|v| v.pow_vartime(&alpha_inv_vec)),
                        state[1].value().map(|v| v.pow_vartime(&alpha_inv_vec)),
                        state[2].value().map(|v| v.pow_vartime(&alpha_inv_vec))
                    ];

                    state[0] = region.assign_advice(|| "s0_sb", config.circuit_params.advice[0], *offset, || after_sb_inv[0])?;
                    state[1] = region.assign_advice(|| "s1_sb", config.circuit_params.advice[1], *offset, || after_sb_inv[1])?;
                    state[2] = region.assign_advice(|| "s2_sb", config.circuit_params.advice[2], *offset, || after_sb_inv[2])?;

                    // second mds multiplication
                    mds_mul(state, region, offset)?;

                    // second inject/add round constants
                    inject_rcs(state, region, offset, 2*round+1)?;

                    Ok(())
                };

                // perform the Rescue-Prime rounds
                for i in 0..config.permutation_params.rounds {
                    rescue_round(&mut region, &mut state, i, &mut offset)?;
                }

                Ok([Number(state[0].clone()), Number(state[1].clone()), Number(state[2].clone())])
            }
        )
    }
}

// helper function to return common parameters struct
fn get_common_params<F: PrimeField>() -> PermutationParameters<F> {
    let state_size: usize = 3;
    let rate: usize = 2;
    let capacity: usize = 1;
    let mds: [[F; 3]; 3] = [
        [
            F::from_str_vartime("27854988750630959170337239780597144027224715023811960992659706878268355039181").unwrap(), 
            F::from_str_vartime("25146695260744508059100624982461970690166157722474767565243652164077487269055").unwrap(), 
            F::from_str_vartime("20045359041216123667749848881863965260443684681509271093016182932435520519586").unwrap()
        ],
        [
            F::from_str_vartime("14489116502293865465195620705098702569149962166993518933952339786917836503875").unwrap(), 
            F::from_str_vartime("13125423966940654332711887575940116829944663267413330181877013057693186361539").unwrap(), 
            F::from_str_vartime("37781904496949962127477230973432217892379931214289750852498713884075794707207").unwrap()
        ],
        [
            F::from_str_vartime("13626913895298938265545264952401615832299228269982032679076937571883280705196").unwrap(),
            F::from_str_vartime("1961062001717124873779753860369853658060849384038305407377314938662537282272").unwrap(),
            F::from_str_vartime("39178371364179396693874733819376491076633720395229958100530484864695867731796").unwrap()
        ]
    ];

    PermutationParameters {
        state_size,
        rate,
        capacity,
        mds
    }
}

// implementation of the Circuit trait for the Poseidon Circuit
impl<F: PrimeField> Circuit<F> for PoseidonCircuit<F> {
    type Config = PoseidonChipConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let advice = [meta.advice_column(), meta.advice_column(), meta.advice_column()];
        let fixed = [meta.fixed_column(), meta.fixed_column(), meta.fixed_column()];
        let instance = meta.instance_column();
        
        let common_params = get_common_params();
        let permutation_params = Poseidon {
            common_params,
            partial_rounds: 57 as usize,
            full_rounds: 8 as usize,
            n: 195 as usize,
            alpha: F::from(5)
        };
        
        PoseidonChip::configure(meta, advice, fixed, instance, permutation_params)
    }

    fn synthesize(&self, config: Self::Config, mut layouter: impl Layouter<F>) -> Result<(), Error> {
        let chip = PoseidonChip::construct(config);
        let result = chip.permute(
            layouter.namespace(|| "poseidon_permutation"),
            self.s0,
            self.s1,
            self.s2
        )?;

        chip.expose_as_public(layouter.namespace(|| "result_s0_ps"), Number(result[0].0.clone()), 0)?;
        chip.expose_as_public(layouter.namespace(|| "result_s1_ps"), Number(result[1].0.clone()), 1)?;
        chip.expose_as_public(layouter.namespace(|| "result_s2_ps"), Number(result[2].0.clone()), 2)?;
        
        Ok(())
    }
}

// implementation of the Circuit trait for the Rescue-Prime Circuit
impl<F: PrimeField> Circuit<F> for RescueCircuit<F> {
    type Config = RescueChipConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let advice = [meta.advice_column(), meta.advice_column(), meta.advice_column()];
        let fixed = [meta.fixed_column(), meta.fixed_column(), meta.fixed_column()];
        let instance = meta.instance_column();
        
        let common_params = get_common_params();
        let permutation_params = RescuePrime {
            common_params,
            rounds: 4,
            alpha: F::from(5),
            alpha_inv: BigUint::from_str("20974350070050476191779096203274386335076221000211055129041463479975432473805").unwrap()
        };
        
        RescueChip::configure(meta, advice, fixed, instance, permutation_params)
    }

    fn synthesize(&self, config: Self::Config, mut layouter: impl Layouter<F>) -> Result<(), Error> {
        let chip = RescueChip::construct(config);
        let result = chip.permute(
            layouter.namespace(|| "rescue_permutation"),
            self.s0,
            self.s1,
            self.s2
        )?;

        chip.expose_as_public(layouter.namespace(|| "result_s0_rs"), Number(result[0].0.clone()), 0)?;
        chip.expose_as_public(layouter.namespace(|| "result_s1_rs"), Number(result[1].0.clone()), 1)?;
        chip.expose_as_public(layouter.namespace(|| "result_s2_rs"), Number(result[2].0.clone()), 2)?;
        
        Ok(())
    }
}


// main function
fn main() {
    use halo2_proofs::dev::MockProver;
    use halo2curves::bls12381::Fr;

    // input words per test case
    let init_s0 = Fr::from(0);
    let init_s1 = Fr::from(1);
    let init_s2 = Fr::from(2);

    // Poseidon circuit struct 
    let circuit_ps = PoseidonCircuit {
        s0: Value::known(init_s0),
        s1: Value::known(init_s1),
        s2: Value::known(init_s2),
    };

    let k: u32 = 10;
    let expected_ps = vec![
        Fr::from_str_vartime("18456658763349757341014058622209659766100673761449600566550821987295786346378").unwrap(),
        Fr::from_str_vartime("37068251774887509885063625701815026138353041152735229476479055620962268601796").unwrap(),
        Fr::from_str_vartime("26763157702141528937904191329664859174584798817251788852101947537759678822298").unwrap()
    ];

    let prover = MockProver::run(k, &circuit_ps, vec![expected_ps]).unwrap();
    assert_eq!(prover.verify(), Ok(()));

    // Rescue-Prime circuit struct
    let circuit_rs = RescueCircuit {
        s0: Value::known(init_s0),
        s1: Value::known(init_s1),
        s2: Value::known(init_s2)
    };

    let expected_rs = vec![
        Fr::from_str_vartime("24676065604765391270595002149851002312234459632041588370575065596694234487355").unwrap(),
        Fr::from_str_vartime("17816234630274911985482882329786621137677061678250510441033034837924655204720").unwrap(),
        Fr::from_str_vartime("32362095325492024327617495591945594977492793418106702586392820666794580085697").unwrap()
    ];

    let prover_1 = MockProver::run(k, &circuit_rs, vec![expected_rs]).unwrap();
    assert_eq!(prover_1.verify(), Ok(()));
}