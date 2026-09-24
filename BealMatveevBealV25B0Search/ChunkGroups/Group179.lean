import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1790
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1791
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1792
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1793
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1794
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1795
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1796
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1797
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1798
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1799

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_179 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 179 + i)) (500 * (10 * 179 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1790
  by_cases h1 : i = 1
  · subst i
    exact chunk_1791
  by_cases h2 : i = 2
  · subst i
    exact chunk_1792
  by_cases h3 : i = 3
  · subst i
    exact chunk_1793
  by_cases h4 : i = 4
  · subst i
    exact chunk_1794
  by_cases h5 : i = 5
  · subst i
    exact chunk_1795
  by_cases h6 : i = 6
  · subst i
    exact chunk_1796
  by_cases h7 : i = 7
  · subst i
    exact chunk_1797
  by_cases h8 : i = 8
  · subst i
    exact chunk_1798
  by_cases h9 : i = 9
  · subst i
    exact chunk_1799
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
