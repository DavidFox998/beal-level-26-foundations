import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1940
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1941
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1942
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1943
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1944
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1945
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1946
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1947
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1948
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1949

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_194 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 194 + i)) (500 * (10 * 194 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1940
  by_cases h1 : i = 1
  · subst i
    exact chunk_1941
  by_cases h2 : i = 2
  · subst i
    exact chunk_1942
  by_cases h3 : i = 3
  · subst i
    exact chunk_1943
  by_cases h4 : i = 4
  · subst i
    exact chunk_1944
  by_cases h5 : i = 5
  · subst i
    exact chunk_1945
  by_cases h6 : i = 6
  · subst i
    exact chunk_1946
  by_cases h7 : i = 7
  · subst i
    exact chunk_1947
  by_cases h8 : i = 8
  · subst i
    exact chunk_1948
  by_cases h9 : i = 9
  · subst i
    exact chunk_1949
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
