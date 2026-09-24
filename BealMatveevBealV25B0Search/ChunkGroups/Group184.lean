import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1840
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1841
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1842
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1843
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1844
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1845
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1846
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1847
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1848
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1849

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_184 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 184 + i)) (500 * (10 * 184 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1840
  by_cases h1 : i = 1
  · subst i
    exact chunk_1841
  by_cases h2 : i = 2
  · subst i
    exact chunk_1842
  by_cases h3 : i = 3
  · subst i
    exact chunk_1843
  by_cases h4 : i = 4
  · subst i
    exact chunk_1844
  by_cases h5 : i = 5
  · subst i
    exact chunk_1845
  by_cases h6 : i = 6
  · subst i
    exact chunk_1846
  by_cases h7 : i = 7
  · subst i
    exact chunk_1847
  by_cases h8 : i = 8
  · subst i
    exact chunk_1848
  by_cases h9 : i = 9
  · subst i
    exact chunk_1849
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
