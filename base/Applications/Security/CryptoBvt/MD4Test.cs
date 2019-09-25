///////////////////////////////////////////////////////////////////////////////
//
//  Microsoft Research Singularity
//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//

using System;
using System.Text;
using System.Security.Cryptography;

public static class MD4Test
{

    public static void GenerateKnownDigests()
    {
        Random random = new Random();

        for (int i = 0; i < 0x40; i++) {
            int length = (random.Next() % 50) + 50;
            byte[]! message = new byte[length];
            random.NextBytes(message);

            byte[]! digest = (!)(byte[])MD4Context.GetDigest(message);

            Console.WriteLine("new KnownBinaryDigest(\"{0}\", \"{1}\");",
                Util.ByteArrayToStringHex(digest),
                Util.ByteArrayToStringHex(message));
        }
    }

    struct KnownBinaryDigest
    {
        public readonly string Digest;
        public readonly string HexMessage;

        public KnownBinaryDigest(string digest, string message)
        {
            this.Digest = digest;
            this.HexMessage = message;
        }
    }

    struct KnownStringDigest
    {
        public readonly string Digest;
        public readonly string TextMessage;

        public KnownStringDigest(string digest, string message)
        {
            this.Digest = digest;
            this.TextMessage = message;
        }
    }

    #region Known Digests

    static readonly KnownBinaryDigest[] _knownBinaryDigests =
    {
        new KnownBinaryDigest("f0bfce358c94b997446f92418a8ff037", "c07a95c4781606e4c60ddc8bf99e43ffc5c597e745f1ba55d5166a3c36006d39dc09eddb2c41f18d7a92f056f9afb90513c510882e4650"),
        new KnownBinaryDigest("a2a637a9435062b1a0ea99da79b43b30", "bf3fef62acc9aec5a0a3aef0b167d283d40a6cb300635c255c642870efe40a96b91e1bec518ee0b0e42ab65601c953abf38cb424d99cce5ce3ca0548a03dd6bb991736934ce5314529bccfd5ad0523"),
        new KnownBinaryDigest("20642ecf402a801b63a84d6bee5c5214", "107d7d6230e5bd1d4fbf098789980fa654fabdea92bf5f0d5b6efb1ccdf8afdda6713723c0748bb35919448cdcaabc91ac2881b2483901511d6f07c1eaa04f56102be1"),
        new KnownBinaryDigest("3db0ec870748f4ce621e7f0390c14e47", "61ece5df6f0990787bd230b0b26a70a477fc946c70e605516dc9c8b8c9ed7cb0c8a52fc043a2423ea888d54b3f560f8030abdf139774a67be69472a540d7ae8d567fe8"),
        new KnownBinaryDigest("ba47a68179ae71f3bdec8076d3616daa", "3aaf60d5ba55c4e710ba1117ba48881e0e681954feb4d9ae2f9cfdd1d947f4bf6d0245804a0a5941b0bf6a2b825bebf84f907fee65940e85d5b1a51d58f20ec8c651a9b70207d3030ed8a33f49ad2cd4b1058149c8065ad9f4c0aa98653ce9bdb0a1"),
        new KnownBinaryDigest("8e3f46b580f612f6689820d6edccb4c0", "31b134f547bc7bdf8cf0ce3b2785d06b5271c500bff7cfc2425c3b9ed2efe68ea848fb227d10398c4c26cde92584821294d0964ceba1a639e271b2ea81dd0d9d0a4093df8aadee413738b4982ae59dbeda280901589aa306a2c1400b5d"),
        new KnownBinaryDigest("6d9c5f91951d6910434748c9d8ee16cf", "0b6f1930dfe5f0a288e6e25414b2ed0d0efcd4f31058d30b44709c8d3dc86de2e3e82d457ffa06b7ce37a0221f0385f01995b243376a3eb29b0deb6f486365bf79ff712c84a78d14f61c25d9b8"),
        new KnownBinaryDigest("90b25ee968b17d38d2c42681b1fd2276", "ec40eaac73a8162aaa79a97ba9710e976f6bd2e1a91f92586b72079e4d1b4465f9ea21ab849cf0bca84e55f78209fd1c055fadba06d706cdad924001a177dd8f3544"),
        new KnownBinaryDigest("06a45aff14d1ec4af4d2cd0345bfed35", "bf4f6312d37a15385bca9bd56274ea98ed6e8a5e22e354fef15bee1b3171c6c23e873ecca24cd93ff19eab0312bcde8db6dfef20aae55fdbfb6420788bf907"),
        new KnownBinaryDigest("98dd4304516ecb0238525c249faac59c", "04d896da351df5a1944a6c843851ec357c61645281a517592863d03d2b61b3f797c1ff3926035798e94e8c6078dba3aa78ebfb2a94b5685ec13db2d14db875329775ec7651b20e7809cc683319b7e04dc026"),
        new KnownBinaryDigest("06d39ef7b937a9a607703136d4adf64b", "40668962e258a078e851864b31d859c803ee2c58c6dc8220c84c3545095c651126f335cc0d120a1eb13a26278380375abfeedd5e"),
        new KnownBinaryDigest("e30551d3ede1ef4bed2666ed88d49bd2", "cdfe63e3689996235a6e8beb75243ea38dbaf0e40da78bb65a9c4814da861a7f067d59f4d2e8a57874fb56cc9a3c0e5bf9b73133ec7a862673ac89cb518148d4530ce5f7cb49d1a51578701250bf1c1e8eec1b2355e6938bf633"),
        new KnownBinaryDigest("e08f1c0e503f1daf4a0814bde5a472b4", "255ed926f2b282788d561690afe68b1d740a73d5b48f6a3d6565247e6d79590197c8ab463c517d5fcd468fc7785b6b3dc9c81f81835dcc96f49bc08c8e030b14fd15f8e73a44e1228d13086d00a3c50afae6b4a459d87d"),
        new KnownBinaryDigest("5926283b00d681d5773aa905d7e236ad", "fb1552a090f0d1c93b7ac96262840385e7fcf36f555f9550d6b692a74f66ba2597beeb25f240919c423e3186d962a875e32fbd5de40ee59c7f01cada5d297ad5bfa4cba399dd93a76b562c172d0f"),
        new KnownBinaryDigest("b8caab8210e57bfa49dc96a4141c3fb8", "740e1cc31fa95d4089d94fa6f076b73e18c35cc6349704dc069c15f28de1ce6e6f8a55cc41665b2b626341ca4a37a230b3181453d14942dc093fbd82936bb3a70be0376520ebfdb2673164d1553a92cffae43e75cd"),
        new KnownBinaryDigest("ab526921f32a481ef9a4221423c55717", "9d254879c201a8d897f6b09abf69003c10c81a61eba0e57187cfadee88ae2c3ed99043111da628fc098f996d21bb7b28cebdd4755b6c8efd40d7f2f253ba4fe8c972c02e26ee1e699f1e585c06774fcb"),
        new KnownBinaryDigest("49adde580b63efa72da477d9ba4ed6c5", "841fcbdab6e36d0245d046b435a84e3fb0a3aefa4c02e09e6ad63c1432f6c887269ecf9b840e128f522ce01dd8b46a75091c56d4a1d007823f2c6fe0a659cf4f08bf8e97d8b2bba1901fa82021c2c6b56cc70a15a0f4"),
        new KnownBinaryDigest("7b9ec86447f0fff3416705a7c8502a50", "55964d5c579e32e8f95c91151826d29c5661b4438128e7607c66ba74de4fbaaf13d938008b5663035e36afc490acad8e992ab4b3ebb1642dafecdff0e4bd09aaa1e2013feed21000fdb0e44a7922d0d0b82bdbb49b07c362740a509e76721fa12c05"),
        new KnownBinaryDigest("4d571a449807de18c896d5518c8314e7", "aeab6e9fc619b3b53acc1ab48c1c0f38b8e1550f9a1e9fcae482728a8b91421d740021254a8b159be75188955a56c382663a67bfd7f6878f0ba4bb44a7292aa98afc3f8c"),
        new KnownBinaryDigest("d1e3ad29b4df00d0e2e82ad7843dc4da", "eaed2cccba27499509708dbeef23502a82467e789119a6cfd1f3bd27df0b5d1636877b4d3af31dce3efa02342e85b705da7f07b6c11469d1475cfbc66922b6fe12768768a803ef8f28af39971672a14b"),
        new KnownBinaryDigest("d81d2be81edf8af4cced6942238f6415", "b74c6003a755221ea905ddf856641c430421b7fd4f5dd78f788d11dbd1bbd5baaf8ab1d556fa6b21654afefd1196d24b1c541250ea4dec5a75d08b1943474cee2f2248ccb247ed0ab69598055fd97de1bbc6"),
        new KnownBinaryDigest("b448014e40d44a7e620431061b420de3", "7da985d0619d575f856e51de1efd0fcdee4d0598d466079a55b5e7fa9c53a95d7d88cf45aa52e62e5ae8689b64b779074f0b8e94b52dea16a1ea7aacb55dc331c5f361962dca229c67d73decfd6c359e3bdf"),
        new KnownBinaryDigest("9768dc037ed3ce03f1d22724f5db2774", "90c515a84f9db8a4bfd73a78fd2437d67055e3da85e8f22cdef0fd1934b5dc70d6b2326caf4b11f8742563c42c5e3fc8c696c448580524a8d2e8ca5fa09f6f0afbc9a24bf1ca262544ea665f852d007fb035529e"),
        new KnownBinaryDigest("245fefc023958a857f6d76db50c3efd1", "9418d18d8a99c781b257d4b658c963bcf4d6fb709f046d9ec422a4e84aaf6b4dd11a66b1d1bd67315fa3919291a92c649dc2bb5f562e5090aa32c867"),
        new KnownBinaryDigest("a500920a9ae3817d1c6816b3fcf6479f", "de3603ec87e53e62b1eb376eca10fc72da0d1bf5404b88f30bf6a2c9d6069ef4ff3c806d8ea609c4ee01ebd784f08b1d541dd024ad72b493ae0fe09142748cab4c426f8e908ee3340457073e5fb06e1b"),
        new KnownBinaryDigest("38c80b639c54953c6c906e921ddada60", "8575b8367a478d88ecbf7ec578817975408a4280fd8cc53a9b20556b7534fda0c526bdffd375d2fae206a4cf646f8bd58dc91f252c9a6df8af7e9a59f12212b8c1ddff52c47aa1cab8479ef6e8f5d52c957fddac14d7742a"),
        new KnownBinaryDigest("cd38041178d9fb3ba75d5f96e304988f", "c44f55da7808c0f4eb0e876f38111327546de4fc760fbaa86dc4724466a4e969d599ff2a4bf0403fde02fce74ebd5c6dca84bf6a8f2e41b495ad6db3967b8d47241d"),
        new KnownBinaryDigest("58bfac3ac5f74300c3c70b6e2ba4e376", "9f12e8dc642ca51e7413d25ab068047ae1e47ed9a7584a959e828ca96274b5c23023bd5be1a75a3dea10cda1c252bd4b9101ab63a543f346c753"),
        new KnownBinaryDigest("fc4d0efd7403af20e26f7846c9d3d35d", "e1a0fcbbff5d0f2a8caba8983a8941ef968aa8d24cc5411761c8521ded3076938e69799ded54ce44b328309fe96871d964535cbc1f80f1"),
        new KnownBinaryDigest("86db265b01b99746cb3b14aa438191c4", "5ee55a360bf23d5c35150ad010a30142bc641f2395a12ef85778b999d4b9740d785d3e08fa9738c0ebd36ad35ea1c8c0521900bb61cd86bdb761df9239a388"),
        new KnownBinaryDigest("c3fb7c36e5c7e95d79315e222a90f1e4", "a1fd57b365f948242b5e38c1375a9ab5b0f846bab9b8abaad6815198b8a587474bef32604a155a59d1db8f0395c4865cc72ae2405dcec1e851addce4a7"),
        new KnownBinaryDigest("0ae97f2485f43dafea128cab4481dd6c", "6b86d6f1764727396b9b9eede8dd29a81512faf4d08ec347ea7d2d4a0e9c3875b1216f082ca34d3e348dbe47a16fe5e3bea997c9e9b2dfddc38e06f919dd2ace62283cc66d207b71c4bcbf42cf7ca57b974a8b65046e8cff4292459d9d54245762f0"),
        new KnownBinaryDigest("74180625f0e3b027bc5a31af7ab79377", "79331e759d2d26052df29c0e46e98b61cf52c5c9f39c3d84dbdbded46f9768dfde972c4878d4ed38de695e0ca583ffb411f354049d26f0ddf59a9ac24f5295968abd2faebc43e8fb658ceb8a3d30df57db29"),
        new KnownBinaryDigest("598f0f4c89c5b9b55eb71b73b776d00b", "7c426341b8a74e52de3a2ae88bd4c882e85450f7cd0b599f113b669fc5bb42e6268f1953267b77076ef109c13aa35fb675aef6038b31f571e9c4307d41ae8d23f743c2fcbb745b6ddd4889dc0198656ddbb02a"),
        new KnownBinaryDigest("cdb03c829486120b7f77fdb1c9b8ad8c", "c43f5bf499a86a624af9c6bf64e6c9f6e063fa0053892542a7196f505ec3a19084765fb8e8ce62130af922e382ca771bce6e8c77b52ac33b19184d803819038657353bed87100e1200e7f6596641c0dda15481f0372adb59b3249ecf81e1daf0f69c"),
        new KnownBinaryDigest("ee324b754479fe1f0eac727532b90008", "4d8f8993be607976cd3369d4d85870dee398124f2d59e13a63723e911e0d0662cab5734d18c0c390bdb30e26494fc6771103f758e34c5ef3ae4f304c21e857c02d070a23e422c622d482"),
        new KnownBinaryDigest("7d6db0dbba1dbea008746ede376c2c5f", "7a4bbbf013abc6801b15ae7e7d577f9fc890776ed55b4ef84245a292ee3cd48361bae3a8f35f1ca05b683caa7f888ccc6583fe925c13bc1ffdc2adce093391"),
        new KnownBinaryDigest("fe7f9dab6ec7de2f87444b4023dbf5a2", "412a1dc273d7ac6873d7136c1ea378b9b8d62d6b3e42264dfdc4ab30b14e9727d75d69556bc9598ed6951f85005000594af416320625a0fe03cfc4ae2b7c"),
        new KnownBinaryDigest("11b24c3637f7c9026cd1e3ea9e51c1e4", "2540eb95c13a234eee7d9e94a823a14dadc451e5bd376421b1bd6a519c04aa625adef94514ba3e1e26a527b46790f7db628217ead996f9eddbcae404cfd1b2e9d33c39ca295b38f38533bf1710b0ba20c58fef19edc089c4e40c6a4ad6"),
        new KnownBinaryDigest("daf7697812aa4bdf35210439c83fc5d5", "4e55f33ee12b572db206492364a6d7e2dd2a10c33e40e298fb12b375e51cf1ee1c4ae46923d2ce8ec998dde8d0c95be2ed022f3f3913fc0e725b42ce78e14795155a0719"),
        new KnownBinaryDigest("ec9c52bf6541e44e2f591ac088c416ff", "6dbe0a5b81f9a663fac831b7d087e2edb1b5094ed6f6c88f0016e75047d275c2411f804424e3b71955aa78931017a75a65a763a5fdcbec76f57a5b6b12551b27526f75b0079ec8cefdf0f82b7e357fe86f8deba06ecfc476330a4fa9884c06ff8e51"),
        new KnownBinaryDigest("155e56998c8a6f255221c841706d3d9f", "a0a2f653c6df95a80dd2c0f8bffb72fb856a7bb882aafe7dfd4f1e46b0e9f89d2cf5de46783924c0d927b7a473118fae155081951298bdf6a379"),
        new KnownBinaryDigest("279a54a10ad9ce5766c80f9aa68556f1", "77c04ff724d922cbca1c2c834b45badf5af35a0aebbf6f305f67638b9337e8a2ffe3ad00893093ca5046c592e8cd364f57b96302486f6ab7501e97bc759737923389846798ba562a5f90b9a4fadd4892311333dad4e55a8f78f5af6a98d654b8"),
        new KnownBinaryDigest("16d60d34d9250a5d7ab8e810a4dce9a0", "325f5f49ceb69d6338a2b8b5c6bc73d6058a62635cbe4d2ff4efa30aeb92893b0095c87de849635d96779c42a1dab2383c93934cf255b173113055df139277a5197db430f4f5eebc2704cce5220a8d193c6acd57ff3c48abe4546cb8f3834904"),
        new KnownBinaryDigest("01c4c8a06a5cb85947f79faee6e888c9", "f6282425824347a5d624ed88cc5107a23ba3a8c420a6dd34084ba08935c8a3bbc8e52ce169f4b92686b128185b2317026415b8e0a03fdf4f4bf01d36a3be6f0e8032bfe625253947e9813e6e7ec4d9e5349d24200fc31a8906dc9578d68282c841"),
        new KnownBinaryDigest("f052aea84646daf743e894cdf39de7f8", "97286431dd3fdc71f61f0071d18617380206994ffebd1835e0488fc07066fe762c632db08003bfe4449dccfb89940b0e619e807c2ef21bda102e5094af1b018f2089456d5966"),
        new KnownBinaryDigest("9f0b66eff9c7e1aff8c0364a33df09f5", "ff47b50b60f01dac4c3d805fd1e68248394852a052b22a34289c3cdaff4e9eb5fae7803578e6baeaf38104572fbc30a89d410b2507c6644d1c80e2c4b342adfd9ecb64e9664dcf538d68acd0add3056c6c933dbd4379ad3382"),
        new KnownBinaryDigest("e5b8d8b5ba714a335cac91297713b40e", "18f804f636b0d407b8635746424f71b8979f19939f497a76581f04f0b9251e30663235d74e9631fcfca61aa2142551ee4b8ae10e1aef93cf7d8d9e17ace34d"),
        new KnownBinaryDigest("efc78f3593004050862070a900b1f0cb", "4527df0f1a9a69006d1d97f92ed76132ce16a42e440f16779e6559c1f8194f1858865dec4641d3b121e0a0fc579aa0a52b6c49953f1e4f35116770b540a80854cd7ea0a87a75eb8c42f30d"),
        new KnownBinaryDigest("dd0faf606a4a99562a59f5eddf9109d1", "6e1a1f04c4b3958ccfbad9393727dbded01e7078d84c2ed9faf82bb680bd534c10ebc7f7486cf08c127c8413a5667052990dbb2382958b21eb460acb88df0b12668c284c60e496642ee3665bc81b349388d81d72012fc97b60a50b01622404337071ac"),
        new KnownBinaryDigest("4e51172bc8aea5c5cabb4d14eb0a5357", "3e24f2b57757f59f2e2f59d0117743b0c1981137c3acebbad8940109df32eb566e1c5463e668fba93a2a4d304b3bf0ebe15471d75f7555913837dce255ebc0fc440262f522dfca599d67fc985fbb"),
        new KnownBinaryDigest("6590509a2a5a94afe6d6f417232c4464", "9da416288ac013f7f8c7c32bae8b19534f6a50eb49d9fbc8018a173af778bc317cc83f3e3fc2353b310b692d5eb41bce8314ad2e0fd025c3a84d2700a9d9ff800a91ae"),
        new KnownBinaryDigest("c3b8b6368323e3ba4d72186527bd308b", "4cdb148c3515ba3d70cd6a4d6e49b6e3cb8e22aca27b95f19b3492580ce923cd053581a8ff20f9f916e853dbe3da925f221bb47c6f0243d14522f10083613186aa9c4838c70de3aa952896ba27ba0ec0a13235f034"),
        new KnownBinaryDigest("f6321f1c7a026655dd110a958b651712", "5d02f2b063dd2ff876b4b6cc3046925a9714380ae7466c88aa8b14305f502c4052043f454517aa067b9cb1e2035a89c72e479a20b82abf16966905d8c8fe982688757a2c074c14806a31"),
        new KnownBinaryDigest("ec4f3d19e1ed7f0fbf973b2f52c38828", "4a958a854f014c0117b60b88274528aedc11d13d7c048b598ddf5dc0e1331ab6869b74810ce4b6d77cfc80707ced52e7df9e386e98f412460930f770a38c20e49b54028cd0a6a2f75bfac1"),
        new KnownBinaryDigest("0932e93d6d46614616890e7488297535", "831bdca08d76e043fbac1d91882d78dbec4633efdc9cd428ebc51638fb40129d3392c3ee5357e22dabdce9ef367003a22dc60a15c7d2a3e646b4b5c75fa848ba99805ef56a8a889563054300b3e5f17ac2740a3435fcd560efdca79ea21bce"),
        new KnownBinaryDigest("cde8caa572037238bc679984e47992a8", "942e55b6110d38a33d75b2c28ea33361c33a05ea9d13849daafd068de2eaf247373f6c84903a69b43c67f6c04a13d14ca946db6816e36680a9b80c1307aac053826a8b4f36aed188d051ae351c"),
        new KnownBinaryDigest("59d402089b2cce628d9472afa258bce4", "53962cb9e49c0e8a3153d8ebdad82e56ac91a6a33edf888215fa755297c5353063e56476e74dc62444f73937774bd3f95a7aa41c8f798673"),
        new KnownBinaryDigest("de4927482c6025bc9924f98779e0e766", "a9a3e927bcf36b1da787f573b86e5ecb815e46a5510bca267cf81c2018a1ea5ff1683daadcfd8803cd19cfc3de85a10c46510d1b3fcdbc9ed9c3abc3d74b05069d96814f31b4ee"),
        new KnownBinaryDigest("e11d15ca495150953358d9a5581d2ee4", "d542d8373b0648f65710dac693ce1f23ac9ed01952c52c8214c925470351da91638946fcf58562d27ab46cc7713e72cf765ea392e3d4320f"),
        new KnownBinaryDigest("cca1c646dd4f5b01bbf8ec6beae60767", "562272e100f2053548630a88232d273bfd9e9d596511d65656d1a5ae48ad8e5636e69f62f0f17ac2679128da684653307c56e53595b6b1444c1c8a2f4c56ec9ad5b3513d"),
        new KnownBinaryDigest("923fe6402e076748bc2de6e8a031d75b", "c44b0c24daf2d3e8fbed107d7431f1c858c17f345a16d3664a7510a58d05b4f416a3b70ad911bac4dd5c502e7ab1d825fad27cf2d10833ae77a5d964e12e5af6391b67d17a"),
        new KnownBinaryDigest("1b5dbdb642bfda82e4388b93e9ddfcbe", "ee4706bb57fec5a5ec999debaabb88c2230e6f0992333756e2af015af45f4a06aa13e335ec16b134e8d2b940c7f6839f6e77f859617054bb10b0d8a7fd6bb08c4f964096d752d50c5d"),
        new KnownBinaryDigest("7c9c416a29c3928dd66e94868f7ef6d3", "21c07af68eeb2b62eb7d67f0a53abf28253c3d09377c222cf131b6edc71ba1ebfc264e94411921ed7b9a7f32255ef005d7af2d99ce5303a49e4d055d343e9ad0dc"),
    };

    /// <summary>
    /// These digests are from RFC 1320.
    /// </summary>
    static readonly KnownStringDigest[] _knownStringDigests =
    {
        new KnownStringDigest("31d6cfe0d16ae931b73c59d7e0c089c0", ""),
        new KnownStringDigest("bde52cb31de33e46245e05fbdbd6fb24", "a"),
        new KnownStringDigest("a448017aaf21d8525fc10ae87aa6729d", "abc"),
        new KnownStringDigest("d9130a8164549fe818874806e1c7014b", "message digest"),
        new KnownStringDigest("d79e1c308aa5bbcdeea8ed63df412da9", "abcdefghijklmnopqrstuvwxyz"),
        new KnownStringDigest("043f8582f241db351ce627e153e7f0e4", "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789"),
        new KnownStringDigest("e33b4ddc9c38f2199c3e7b164fcc0536", "12345678901234567890123456789012345678901234567890123456789012345678901234567890"),
    };

    #endregion

    public static void VerifyKnownDigests()
    {
        foreach (KnownBinaryDigest known in _knownBinaryDigests) {
            byte[]! message = Util.HexStringToByteArray(known.HexMessage);
            byte[]! knownDigest = Util.HexStringToByteArray(known.Digest);
            byte[]! computedDigest = (!)MD4Context.GetDigest(message).ToArray();

            if (Util.CompareArraySpans(knownDigest, 0, computedDigest, 0, MD4Context.DigestLength) != 0) {
                Console.WriteLine("*** DIGESTS DIFFER! ***");
                Console.WriteLine("Known digest: " + knownDigest);
                Console.WriteLine("Computed digest: " + computedDigest);
                Console.WriteLine("MD4 BVT FAILED.");
                return;
            }
        }

        foreach (KnownStringDigest known in _knownStringDigests) {
            byte[]! message = Encoding.ASCII.GetBytes(known.TextMessage);
            byte[]! knownDigest = Util.HexStringToByteArray(known.Digest);
            byte[]! computedDigest = (!)MD4Context.GetDigest(message).ToArray();

            if (Util.CompareArraySpans(knownDigest, 0, computedDigest, 0, MD4Context.DigestLength) != 0) {
                Console.WriteLine("*** DIGESTS DIFFER! ***");
                Console.WriteLine("Message:           " + known.TextMessage);
                Console.WriteLine("Known digest:      " + knownDigest);
                Console.WriteLine("Computed digest:   " + computedDigest);
                Console.WriteLine("MD4 BVT FAILED.");
                return;
            }
        }

        Console.WriteLine("PASSED: MD4 BVT");
        Console.WriteLine("Verified {0} known string digests.", _knownStringDigests.Length);
        Console.WriteLine("Verified {0} known binary digests.", _knownBinaryDigests.Length);
    }
}
