import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1290
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1291
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1292
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1293
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1294
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1295
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1296
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1297
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1298
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1299

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_129 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 129 + i)) (500 * (10 * 129 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1290
  by_cases h1 : i = 1
  · subst i
    exact chunk_1291
  by_cases h2 : i = 2
  · subst i
    exact chunk_1292
  by_cases h3 : i = 3
  · subst i
    exact chunk_1293
  by_cases h4 : i = 4
  · subst i
    exact chunk_1294
  by_cases h5 : i = 5
  · subst i
    exact chunk_1295
  by_cases h6 : i = 6
  · subst i
    exact chunk_1296
  by_cases h7 : i = 7
  · subst i
    exact chunk_1297
  by_cases h8 : i = 8
  · subst i
    exact chunk_1298
  by_cases h9 : i = 9
  · subst i
    exact chunk_1299
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
