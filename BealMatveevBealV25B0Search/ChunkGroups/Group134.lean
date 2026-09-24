import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1340
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1341
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1342
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1343
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1344
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1345
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1346
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1347
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1348
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1349

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_134 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 134 + i)) (500 * (10 * 134 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1340
  by_cases h1 : i = 1
  · subst i
    exact chunk_1341
  by_cases h2 : i = 2
  · subst i
    exact chunk_1342
  by_cases h3 : i = 3
  · subst i
    exact chunk_1343
  by_cases h4 : i = 4
  · subst i
    exact chunk_1344
  by_cases h5 : i = 5
  · subst i
    exact chunk_1345
  by_cases h6 : i = 6
  · subst i
    exact chunk_1346
  by_cases h7 : i = 7
  · subst i
    exact chunk_1347
  by_cases h8 : i = 8
  · subst i
    exact chunk_1348
  by_cases h9 : i = 9
  · subst i
    exact chunk_1349
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
