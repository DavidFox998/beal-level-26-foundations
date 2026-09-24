import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1260
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1261
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1262
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1263
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1264
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1265
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1266
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1267
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1268
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1269

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_126 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 126 + i)) (500 * (10 * 126 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1260
  by_cases h1 : i = 1
  · subst i
    exact chunk_1261
  by_cases h2 : i = 2
  · subst i
    exact chunk_1262
  by_cases h3 : i = 3
  · subst i
    exact chunk_1263
  by_cases h4 : i = 4
  · subst i
    exact chunk_1264
  by_cases h5 : i = 5
  · subst i
    exact chunk_1265
  by_cases h6 : i = 6
  · subst i
    exact chunk_1266
  by_cases h7 : i = 7
  · subst i
    exact chunk_1267
  by_cases h8 : i = 8
  · subst i
    exact chunk_1268
  by_cases h9 : i = 9
  · subst i
    exact chunk_1269
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
