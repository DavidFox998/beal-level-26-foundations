import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1880
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1881
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1882
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1883
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1884
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1885
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1886
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1887
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1888
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1889

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_188 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 188 + i)) (500 * (10 * 188 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1880
  by_cases h1 : i = 1
  · subst i
    exact chunk_1881
  by_cases h2 : i = 2
  · subst i
    exact chunk_1882
  by_cases h3 : i = 3
  · subst i
    exact chunk_1883
  by_cases h4 : i = 4
  · subst i
    exact chunk_1884
  by_cases h5 : i = 5
  · subst i
    exact chunk_1885
  by_cases h6 : i = 6
  · subst i
    exact chunk_1886
  by_cases h7 : i = 7
  · subst i
    exact chunk_1887
  by_cases h8 : i = 8
  · subst i
    exact chunk_1888
  by_cases h9 : i = 9
  · subst i
    exact chunk_1889
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
