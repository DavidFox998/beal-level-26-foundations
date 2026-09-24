import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1870
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1871
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1872
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1873
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1874
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1875
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1876
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1877
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1878
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1879

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_187 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 187 + i)) (500 * (10 * 187 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1870
  by_cases h1 : i = 1
  · subst i
    exact chunk_1871
  by_cases h2 : i = 2
  · subst i
    exact chunk_1872
  by_cases h3 : i = 3
  · subst i
    exact chunk_1873
  by_cases h4 : i = 4
  · subst i
    exact chunk_1874
  by_cases h5 : i = 5
  · subst i
    exact chunk_1875
  by_cases h6 : i = 6
  · subst i
    exact chunk_1876
  by_cases h7 : i = 7
  · subst i
    exact chunk_1877
  by_cases h8 : i = 8
  · subst i
    exact chunk_1878
  by_cases h9 : i = 9
  · subst i
    exact chunk_1879
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
