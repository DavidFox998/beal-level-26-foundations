import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1500
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1501
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1502
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1503
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1504
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1505
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1506
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1507
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1508
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1509

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_150 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 150 + i)) (500 * (10 * 150 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1500
  by_cases h1 : i = 1
  · subst i
    exact chunk_1501
  by_cases h2 : i = 2
  · subst i
    exact chunk_1502
  by_cases h3 : i = 3
  · subst i
    exact chunk_1503
  by_cases h4 : i = 4
  · subst i
    exact chunk_1504
  by_cases h5 : i = 5
  · subst i
    exact chunk_1505
  by_cases h6 : i = 6
  · subst i
    exact chunk_1506
  by_cases h7 : i = 7
  · subst i
    exact chunk_1507
  by_cases h8 : i = 8
  · subst i
    exact chunk_1508
  by_cases h9 : i = 9
  · subst i
    exact chunk_1509
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
