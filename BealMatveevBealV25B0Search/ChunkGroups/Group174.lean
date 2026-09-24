import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1740
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1741
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1742
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1743
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1744
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1745
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1746
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1747
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1748
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1749

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_174 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 174 + i)) (500 * (10 * 174 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1740
  by_cases h1 : i = 1
  · subst i
    exact chunk_1741
  by_cases h2 : i = 2
  · subst i
    exact chunk_1742
  by_cases h3 : i = 3
  · subst i
    exact chunk_1743
  by_cases h4 : i = 4
  · subst i
    exact chunk_1744
  by_cases h5 : i = 5
  · subst i
    exact chunk_1745
  by_cases h6 : i = 6
  · subst i
    exact chunk_1746
  by_cases h7 : i = 7
  · subst i
    exact chunk_1747
  by_cases h8 : i = 8
  · subst i
    exact chunk_1748
  by_cases h9 : i = 9
  · subst i
    exact chunk_1749
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
