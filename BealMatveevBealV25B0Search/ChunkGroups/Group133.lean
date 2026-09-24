import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1330
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1331
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1332
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1333
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1334
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1335
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1336
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1337
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1338
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1339

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_133 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 133 + i)) (500 * (10 * 133 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1330
  by_cases h1 : i = 1
  · subst i
    exact chunk_1331
  by_cases h2 : i = 2
  · subst i
    exact chunk_1332
  by_cases h3 : i = 3
  · subst i
    exact chunk_1333
  by_cases h4 : i = 4
  · subst i
    exact chunk_1334
  by_cases h5 : i = 5
  · subst i
    exact chunk_1335
  by_cases h6 : i = 6
  · subst i
    exact chunk_1336
  by_cases h7 : i = 7
  · subst i
    exact chunk_1337
  by_cases h8 : i = 8
  · subst i
    exact chunk_1338
  by_cases h9 : i = 9
  · subst i
    exact chunk_1339
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
