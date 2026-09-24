import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1920
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1921
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1922
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1923
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1924
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1925
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1926
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1927
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1928
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1929

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_192 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 192 + i)) (500 * (10 * 192 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1920
  by_cases h1 : i = 1
  · subst i
    exact chunk_1921
  by_cases h2 : i = 2
  · subst i
    exact chunk_1922
  by_cases h3 : i = 3
  · subst i
    exact chunk_1923
  by_cases h4 : i = 4
  · subst i
    exact chunk_1924
  by_cases h5 : i = 5
  · subst i
    exact chunk_1925
  by_cases h6 : i = 6
  · subst i
    exact chunk_1926
  by_cases h7 : i = 7
  · subst i
    exact chunk_1927
  by_cases h8 : i = 8
  · subst i
    exact chunk_1928
  by_cases h9 : i = 9
  · subst i
    exact chunk_1929
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
