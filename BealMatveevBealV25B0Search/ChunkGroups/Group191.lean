import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1910
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1911
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1912
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1913
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1914
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1915
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1916
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1917
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1918
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1919

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_191 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 191 + i)) (500 * (10 * 191 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1910
  by_cases h1 : i = 1
  · subst i
    exact chunk_1911
  by_cases h2 : i = 2
  · subst i
    exact chunk_1912
  by_cases h3 : i = 3
  · subst i
    exact chunk_1913
  by_cases h4 : i = 4
  · subst i
    exact chunk_1914
  by_cases h5 : i = 5
  · subst i
    exact chunk_1915
  by_cases h6 : i = 6
  · subst i
    exact chunk_1916
  by_cases h7 : i = 7
  · subst i
    exact chunk_1917
  by_cases h8 : i = 8
  · subst i
    exact chunk_1918
  by_cases h9 : i = 9
  · subst i
    exact chunk_1919
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
