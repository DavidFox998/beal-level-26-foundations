import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1400
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1401
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1402
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1403
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1404
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1405
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1406
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1407
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1408
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1409

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_140 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 140 + i)) (500 * (10 * 140 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1400
  by_cases h1 : i = 1
  · subst i
    exact chunk_1401
  by_cases h2 : i = 2
  · subst i
    exact chunk_1402
  by_cases h3 : i = 3
  · subst i
    exact chunk_1403
  by_cases h4 : i = 4
  · subst i
    exact chunk_1404
  by_cases h5 : i = 5
  · subst i
    exact chunk_1405
  by_cases h6 : i = 6
  · subst i
    exact chunk_1406
  by_cases h7 : i = 7
  · subst i
    exact chunk_1407
  by_cases h8 : i = 8
  · subst i
    exact chunk_1408
  by_cases h9 : i = 9
  · subst i
    exact chunk_1409
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
