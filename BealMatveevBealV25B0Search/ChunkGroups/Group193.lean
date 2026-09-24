import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1930
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1931
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1932
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1933
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1934
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1935
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1936
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1937
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1938
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1939

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_193 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 193 + i)) (500 * (10 * 193 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1930
  by_cases h1 : i = 1
  · subst i
    exact chunk_1931
  by_cases h2 : i = 2
  · subst i
    exact chunk_1932
  by_cases h3 : i = 3
  · subst i
    exact chunk_1933
  by_cases h4 : i = 4
  · subst i
    exact chunk_1934
  by_cases h5 : i = 5
  · subst i
    exact chunk_1935
  by_cases h6 : i = 6
  · subst i
    exact chunk_1936
  by_cases h7 : i = 7
  · subst i
    exact chunk_1937
  by_cases h8 : i = 8
  · subst i
    exact chunk_1938
  by_cases h9 : i = 9
  · subst i
    exact chunk_1939
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
