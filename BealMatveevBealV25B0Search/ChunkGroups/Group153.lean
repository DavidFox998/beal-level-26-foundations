import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1530
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1531
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1532
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1533
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1534
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1535
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1536
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1537
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1538
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1539

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_153 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 153 + i)) (500 * (10 * 153 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1530
  by_cases h1 : i = 1
  · subst i
    exact chunk_1531
  by_cases h2 : i = 2
  · subst i
    exact chunk_1532
  by_cases h3 : i = 3
  · subst i
    exact chunk_1533
  by_cases h4 : i = 4
  · subst i
    exact chunk_1534
  by_cases h5 : i = 5
  · subst i
    exact chunk_1535
  by_cases h6 : i = 6
  · subst i
    exact chunk_1536
  by_cases h7 : i = 7
  · subst i
    exact chunk_1537
  by_cases h8 : i = 8
  · subst i
    exact chunk_1538
  by_cases h9 : i = 9
  · subst i
    exact chunk_1539
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
