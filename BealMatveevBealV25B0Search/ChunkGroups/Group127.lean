import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1270
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1271
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1272
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1273
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1274
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1275
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1276
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1277
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1278
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1279

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_127 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 127 + i)) (500 * (10 * 127 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1270
  by_cases h1 : i = 1
  · subst i
    exact chunk_1271
  by_cases h2 : i = 2
  · subst i
    exact chunk_1272
  by_cases h3 : i = 3
  · subst i
    exact chunk_1273
  by_cases h4 : i = 4
  · subst i
    exact chunk_1274
  by_cases h5 : i = 5
  · subst i
    exact chunk_1275
  by_cases h6 : i = 6
  · subst i
    exact chunk_1276
  by_cases h7 : i = 7
  · subst i
    exact chunk_1277
  by_cases h8 : i = 8
  · subst i
    exact chunk_1278
  by_cases h9 : i = 9
  · subst i
    exact chunk_1279
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
