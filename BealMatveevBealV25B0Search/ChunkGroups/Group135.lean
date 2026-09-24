import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1350
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1351
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1352
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1353
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1354
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1355
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1356
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1357
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1358
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1359

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_135 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 135 + i)) (500 * (10 * 135 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1350
  by_cases h1 : i = 1
  · subst i
    exact chunk_1351
  by_cases h2 : i = 2
  · subst i
    exact chunk_1352
  by_cases h3 : i = 3
  · subst i
    exact chunk_1353
  by_cases h4 : i = 4
  · subst i
    exact chunk_1354
  by_cases h5 : i = 5
  · subst i
    exact chunk_1355
  by_cases h6 : i = 6
  · subst i
    exact chunk_1356
  by_cases h7 : i = 7
  · subst i
    exact chunk_1357
  by_cases h8 : i = 8
  · subst i
    exact chunk_1358
  by_cases h9 : i = 9
  · subst i
    exact chunk_1359
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
