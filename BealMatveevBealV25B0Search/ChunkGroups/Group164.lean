import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1640
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1641
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1642
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1643
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1644
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1645
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1646
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1647
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1648
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1649

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_164 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 164 + i)) (500 * (10 * 164 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1640
  by_cases h1 : i = 1
  · subst i
    exact chunk_1641
  by_cases h2 : i = 2
  · subst i
    exact chunk_1642
  by_cases h3 : i = 3
  · subst i
    exact chunk_1643
  by_cases h4 : i = 4
  · subst i
    exact chunk_1644
  by_cases h5 : i = 5
  · subst i
    exact chunk_1645
  by_cases h6 : i = 6
  · subst i
    exact chunk_1646
  by_cases h7 : i = 7
  · subst i
    exact chunk_1647
  by_cases h8 : i = 8
  · subst i
    exact chunk_1648
  by_cases h9 : i = 9
  · subst i
    exact chunk_1649
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
