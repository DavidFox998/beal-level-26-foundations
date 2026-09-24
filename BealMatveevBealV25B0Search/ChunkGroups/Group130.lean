import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1300
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1301
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1302
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1303
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1304
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1305
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1306
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1307
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1308
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1309

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_130 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 130 + i)) (500 * (10 * 130 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1300
  by_cases h1 : i = 1
  · subst i
    exact chunk_1301
  by_cases h2 : i = 2
  · subst i
    exact chunk_1302
  by_cases h3 : i = 3
  · subst i
    exact chunk_1303
  by_cases h4 : i = 4
  · subst i
    exact chunk_1304
  by_cases h5 : i = 5
  · subst i
    exact chunk_1305
  by_cases h6 : i = 6
  · subst i
    exact chunk_1306
  by_cases h7 : i = 7
  · subst i
    exact chunk_1307
  by_cases h8 : i = 8
  · subst i
    exact chunk_1308
  by_cases h9 : i = 9
  · subst i
    exact chunk_1309
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
