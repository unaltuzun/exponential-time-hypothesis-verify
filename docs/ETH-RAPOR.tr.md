# OpenAI "ETH is False" Lean kanıtı — bağımsız doğrulama ve hassasiyet genişletmesi

Tarih: 28 Ekim 2026. Bu belge üç işi bir araya getirir: (A) kanıtın çekirdek düzeyinde bağımsız doğrulanması,
(B) Appendix D'deki `P₀ ≤ Cs` varsayımının genişletilmesinin kaynağa karşı denetimi, (C) bu genişletmenin
aritmetik çekirdeği için yazılan Lean sertifikasının kontrolü. Kanıtın yazarları OpenAI'dir; burada yapılan
yalnızca doğrulamadır.

## 1. Kaynak

- Repo: `github.com/openai/math`, commit `7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a`
- Makale: `preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/`
  (`build/quantitative-reduction.tex`, `build/quantitative-contraction.tex`, `build/main_full_version.tex`)
- SHA-256 (hepsi beklenenle eşleşti):
  - `lean/ComparatorChallenges/SubexponentialSAT.lean` → `4183b2057cff350d66848215ff7167196dfc20e1891b598fdddea59077a76685`
  - `lean/ComparatorChallenges/SubexponentialSAT.json` → `debbfdc9c01104d2369be80da5180978275106df8b685f693fba7ce7da7c5b19`
  - `lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/Final.lean` → `040360a8465957622d934e5f1bb4f2cce8dab950e78f52033fbf70da493184f5`

## 2. (A) Çekirdek doğrulaması — sonuç: KERNEL-VERIFIED

Ortam: macOS 26.5.1, Apple M5 Max (18 çekirdek), 128 GiB RAM. Lean 4.34.1
(commit `5045d0056413266e57c625dcd7c365b10e377c52`), Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`
(8.908 önbellek dosyası, Mathlib yeniden derlenmedi).

| Hedef | Çıkış | Süre | Uyarı / hata |
|---|---|---|---|
| `ComparatorChallenges.SubexponentialSAT` (ifade dosyası) | 0 | 27,8 sn | 1 uyarı: tasarım gereği tek `sorry` |
| `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Final` | 0 | 2.079,6 sn (11.492 iş) | 0 / 0 |
| `OAI.Algorithms.SubexponentialSAT.Main` | 0 | 413,9 sn (12.014 iş) | 0 / 0 |

`#print axioms` (üç ayrı yoldan çalıştırıldı, sonuç aynı): şu teoremlerin hepsi yalnızca
`[propext, Classical.choice, Quot.sound]` aksiyomlarına dayanıyor:
`exact_count_and_sat`, `exact_count_eth`, `sat_polynomial_space`, `original_sat_main`, `compiled_exact_count_and_sat`
(hepsi `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace` içinde). `sorryAx` ya da özel aksiyom yok.

Comparator (ifade eşitliği): `landrun` Linux'a özgü olduğu için ayrı bir Ubuntu 26.04 sanal makinesinde
(Lima) çalıştırıldı. Araçlar: comparator `d03acab1` (v4.34.0), lean4export `076e8e57` (v4.34.0, Lean 4.34.1 ile
derlendi), landrun 0.1.18. Her iki modül sandbox içinde sıfırdan derlendi. Çıktı:

```
Running Lean default kernel on solution.
Lean default kernel accepts the solution
Your solution is okay!
Finished with result: success      (33 dk 44 sn)
```

Sapmalar: Comparator macOS'ta değil Linux VM'de çalıştı; README'deki `--pty` yerine `systemd-run --pipe`
kullanıldı (aynı `RestrictAddressFamilies=~AF_UNIX` kısıtıyla); isteğe bağlı nanoda çekirdeği kapalıydı
(challenge JSON'u bunu kapalı tanımlıyor).

Çapraz kontrol: `anthropics/formal-math` @ `16a5ce41…` (`eth/`) derlendi; `MainResults.ethIsFalse` ve
`MainResults.mainTheorem` yalnızca üç standart aksiyoma dayanıyor.

### Lean'de kanıtlanan sınır tam olarak ne?

`exact_count_and_sat`: her `k ≥ 2` için tek bir makine, genişliği en fazla k olan her CNF formülü için tam
sayımı ve tatmin edilebilirliği hesaplıyor; süre

```
runtimeBound = C · (bits+1)^d · 2^(A · n·(log log(n+16))² / √log(n+16))     (log = doğal logaritma)
```

ve tüm ara adımlarda polinom alan. Bu `2^{δn}`'den hızlı olduğu için ETH'yi yanlışlar; P = NP demek değildir.
Makaledeki keskin `2^{O(n/√log n)}` sınırına göre fazladan bir `(log log n)²` çarpanı var; keskin sınır Lean'de
değil, yalnızca makalede.

### İfadenin sadakati (30 Ekim 2026'da incelendi)

Lean, formal ifadenin kanıtlandığını garanti eder; ifadenin doğru şeyi söylediğini değil. Bu yüzden
`ComparatorChallenges/SubexponentialSAT.lean`'deki tanımlar (220 satır; 219–220 yalnızca `end`) tek tek okundu.
Bu bir keşif değil, olumsuz bir bulgudur: ifadede hile arandı, bulunamadı. İnceleme iki yapay zekâ
okumasına dayanıyor ve bağımsız uzman incelemesinin yerini tutmaz.

- **Sınırdaki n** (199, 210–211; 136–139): `F : SAT.CNF (Fin n)`, yani n değişken sayısı. Üstel kısım
  `runtimeScale n`; girdi uzunluğu yalnızca `(inputBits+1)^degree` polinom çarpanında. (Sınır girdi uzunluğu
  cinsinden olsaydı ETH çürümezdi; durum bu değil.)

- **Makine modeli** (`PrimitiveMachine`, 92–124): sonlu durumlu, çok şeritli Turing makinesi; alfabe
  `Option Bool` (boş, 0, 1). Her adımda tek bir şerit okunur ve ya durulur ya da tek bir Mathlib `TM0.Stmt`
  uygulanır: bir hücre sola/sağa git ya da bir sembol yaz (`Mathlib/Computability/TuringMachine/
  PostTuringMachine.lean`:118–120, `Tape.lean`:436–439, 542–543). Aritmetik ya da kehanet (oracle) işlemi yok;
  standart modelden bile zayıf (adım başına tek şerit).
- **Tekdüzelik:** niceleyici sırası `∀ k, ∃ makine ∃ sabitler, ∀ n ∀ F`. Tek bir sabit makine (k'ye bağlı)
  bütün formülleri çözüyor; n'ye göre değişen devre ya da tablo değil.
- **Zaman:** `Trace` deterministik adım fonksiyonunun tam `time` adımda durma (`state = Sum.inl …`)
  konfigürasyonuna ulaştığını söylüyor; yani `time` gerçek çalışma süresi, her adım birim maliyet.
- **Girdi:** `encodeCNF` = n'nin birli (unary) kodu + klozların listesi, literal kodları `2v+b` yine birli.
  Birli kodlama girdiyi büyütür ama zararsız: genişliği ≤ k olan farklı kloz sayısı `O((2n)^k)`, dolayısıyla
  `formulaBitLength = n^{O(k)}` ve sınırdaki `(bits+1)^d` çarpanı sabit k için `poly(n) = 2^{o(n)}`.
- **Çıktı:** sayım şeridinde `SAT.count F`'in ikili yazımı, cevap şeridinde ve son durumda `0 < count`.
  `SAT.count` = n değişkenli tüm atamalar içinde sağlayanların sayısı (Mathlib `Finset`). Yani tam #k-SAT.
- **Sınır:** `runtimeScale n = n·(log log(n+16))²/√log(n+16) = o(n)`.

**Sonuç:** İfade şunu söylüyor: her sabit k ≥ 2 için, k-CNF formüllerindeki sağlayan atamaları tam sayan ve
`poly(|F|)·2^{O(n(log log n)²/√log n)} = 2^{o(n)}` adımda duran deterministik çok şeritli bir Turing makinesi
var. k = 3 alınınca bu doğrudan ETH'nin değillemesi (ETH: bir δ > 0 için 3-SAT `2^{δn}` zamanda
çözülemez); SETH, ETH'yi gerektirdiği için SETH de yanlış olur. Kalan güven tabanı: Lean çekirdeği,
Mathlib'in `Turing.Tape`/`TM0` tanımları ve challenge dosyasının kendisi (hash'i doğrulandı, Comparator ile
çözümle eşleştirildi).

## 3. (B) Appendix D: `P₀ ≤ Cs` → `P₀ ≤ s(log s)^K`

Teorem (`quantitative-reduction.tex`:26–49) girdileri `(ℤ/2^{P₀}ℤ)[V]/(V^ℓ)` halkasında, `1 ≤ P₀, ℓ ≤ Cs`
varsayımıyla alır. Kaynağın parametreleri (`quantitative-contraction.tex`):

- `λ = ⌈log₂ s⌉`, `ε = 1/(128·1024)`, `u_d = ⌊ελ/2^d⌋`, `a_d = 2·Σ_{j≤d} u_j`, `L = 2^{a_d}` (satır 82–91)
- Çocuk ağın kenarı `≤ 3M/32 < M/8`; `M ≤ Cs·8^{−d}`; yaprak `M ≤ H = ⌈s/⌊√λ⌋⌉` (85, 95, 525–526)
- Aktif çağrılarda `u ≥ λ^{4/5}`, `a_d ≤ 4ελ`, `L ≤ s^{1/1000}` (100–104)
- `D_t = L/2^{v₂(t)}`, `h = ⌈3M/u⌉`, `p_t = p + 8hD_t + 8M(a+1)` (252–264)

Hassasiyet ispatı (348–368) iki adımdır:

1. Giriş: `p ≤ s·λ^{O(1)}·2^{a_{d−1}}`. Kaynak bunu kökte "`P₀ ≤ Cs` olduğundan" başlatır (354);
   `P₀`'ın kullanıldığı tek yer burası.
2. Çocuk: `q_t > 0 ⇒ D_t ≥ 2^{a_{d−1}+u}` (359–361) ve `M > H` olduğundan `p_t = O_C(M·D_t/u)`;
   çünkü `u ≥ λ^{4/5}` için `2^u` her sabit λ kuvvetini ezer.

Genişletme: `P₀ ≤ s·λ^K` alınırsa 1. adım yine tutar (yalnızca λ'nın üssü K kadar artar; derinlikteki
artışlar `P₀`'dan bağımsız). 2. adımda `M > H ≥ s/√λ` kullanılınca gereken
`√λ · λ^{K+O(1)} · u ≤ C′·2^u` (yani `u·λ^{K+O(1)} ≤ C′·2^u`, √λ üsse katılarak) yine `u ≥ λ^{4/5}` ile sağlanır.
Mod sayısı `exp(O(√(M·p_t/D))) = exp(O(M/√u))` (457–460) yalnızca `p_t = O(M·D_t/u)`'yu kullandığından
süre `2^{O(s/√log s)}` aynen kalır; sabitler ve küçük-s eşiği K'ya bağlı olur.
**Durum:** kaynağa karşı elle denetlendi; aritmetik çekirdeği §5'te Lean'de kanıtlandı.

## 4. Ağırlıklı tablo sonucu

Rasyonel ağırlıklı tablolar `φ_a` için `Z = Σ_x ∏_a φ_a(x|_{S_a})`. Her tablonun girdileri kendi ortak
paydası `q_a` ile ölçeklenirse (`p̃_a` paylar), `Ω = ∏ q_a` için hesaplanan şey `ΩZ = Σ_x ∏_a p̃_a(x)`
tamsayısıdır. Negatif ağırlıklarla birlikte tam geri almak için:

```
P₀ ≥ n + Σ_a ⌈log₂ max|p̃_a|⌉ + 2
```

(`P₀ = ⌈log₂ Ω⌉` yeterli değildir.) Kaynağın sayım ispatı aynı ilkeyi kullanır: `P₀ = n+1` çünkü
`0 ≤ #F ≤ 2^n` (`quantitative-reduction.tex`:86–93).

Koşullar: (i) tablo sayısı ve toplam arite `O(n)` (sabit yoğunluk, `s = Θ(n)`); (ii) sınırlı arite, tablolar
kaynaktaki cümle kodlamasıyla ağa çevrilir; (iii) paylar ve paydalar tablo başına polylog bit.
O zaman `P₀ = O(s(log s)^K)` ve §3 ile `Z`, `(s+𝓛)^{O(1)}·2^{O(n/√log n)}` sürede ve polinom alanda tam
hesaplanır. Yoğun durumda kaynak `O(n log log n)` tel kullanır ve sınır keskin değildir. **Durum:** makale
düzeyinde, koşullu; Lean'de değil.

## 5. (C) Lean sertifikası: `precision_extension`

Dosya: `lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/PrecisionExtensionCore.lean` (451 satır,
yalnızca çekirdek Lean, Mathlib yok; GLM-5.3 tarafından yazıldı, ayrı bir çalışma kopyasında).

```lean
theorem SubexponentialSAT.PrecisionExtensionCore.precision_extension
    (B N d u : Nat) (hB : B ≤ 2 ^ 20) (hN : 2 ^ 640 ≤ N)
    (hd : 2 ^ (6 * d) ≤ 2 ^ 18 * N) (hu : u = N / 2 ^ (17 + d)) :
    2 ^ u ≥ N ^ (B + 2) * u * 2 ^ 18
```

Burada `N = λ`, `u = u_d` (ε = 2^{−17}). Bağımsız kontrol (Lean 4.34.1, repo dışında): derleme başarılı,
yalnızca zararsız "exponent 512" uyarısı; `sorry`, `axiom`, `native_decide`, `extern` yok;
`#print axioms` → `[propext, Classical.choice, Quot.sound]`.

Sınırlar:
- `hd` varsayımı kaynaktaki derinlik sınırından gelir: `8^d < C√λ ⇒ 2^{6d} < C²λ`. Bu dosyadaki sabit 18
  yalnızca `C ≤ 512` için doğru. **Giderildi (30 Ekim):** `PrecisionExtensionGeneral.lean`'deki
  `precision_extension_general`, `C² ≤ 2^(18+c)` olacak şekilde seçilen bir `c` ve `2^(640+8c) ≤ N` eşiğiyle
  her C için aynı sonucu kanıtlıyor; eski teorem `c = 0` özel hali olarak türetiliyor. Claude Fable yazdı;
  Mac'te bağımsız olarak kontrol edildi (çıkış 0, `sorry` yok, üç standart aksiyom; sha256 `cced7e0f…`).
- Yalnızca `B ≤ 2^20` kapsanıyor ("her sabit B" değil).
- Eşik `λ ≥ 2^640`, yani `s ≥ 2^(2^640)`: asimptotik teorem için meşru, pratik anlamı yok.
- Bu yalnızca aritmetik çekirdek. Eşitsizliğin makaledeki ispat için yeterli olduğu (§3) elle yapılmış bir
  akıl yürütme; keskin sınırın Lean'e taşınması bunun çok ötesinde.

## 6. Önceki bir taslakta bulunan hatalar (tekrarlanmaması için)

- Kaynakta olmayan dört mekanizma varsayılmış: `u_d = max(1,·)`, "iki aşamalı düğüm bölme",
  `s^{−Θ(1)}` hata analizi, `s ≥ exp(c√log N)` kısıtı. Hiçbiri kaynakta yok; aritmetik tam (2-adik),
  yaklaşık hata terimi yok.
- `D_t = 𝓛/2^{v₂(t)}` yazılmış (𝓛 açıklama uzunluğu); doğrusu `D_t = L/2^i`, `L = 2^{a_d}`.
- Kenar takvimi `M/2` varsayılmış; doğrusu `< M/8`.
- `u = 1` ve `M = O(log s)` olan bir "yaprak rejimi" varsayılmış; aktif yolda `u ≥ λ^{4/5}`, yaprak `M ≤ H`.
- `P₀ = ⌈log₂ Ω⌉` (bkz. §4).
- `s = Θ(n(log n)^c)` için "daha zayıf subeksponansiyel" yalnızca `c < 1/2` ise doğru.

## 7. Açık kalanlar

1. ~~`precision_extension`'ı genel C için genellemek.~~ Yapıldı (`precision_extension_general`, §5).
   Sıradaki aynı türden iş: `B ≤ 2^20` kısıtını B'ye bağlı bir eşikle kaldırmak.
2. §3'teki "yeterlilik" adımını ve §4'teki ağırlıklı kodlamayı biçimselleştirmek.
3. Lean'deki ifade tanımlarının "ETH yanlış" iddiasına sadakati: incelendi (30 Ekim), hile bulunamadı; bağımsız
   uzman incelemesi bekleniyor (§2, "İfadenin sadakati"). İnceleme iki yapay zekâ okumasına dayanıyor.
4. Keskin `2^{O(n/√log n)}` sınırının Lean'de kanıtı (bugün yalnızca `(log log n)²` çarpanlı sürüm var).
