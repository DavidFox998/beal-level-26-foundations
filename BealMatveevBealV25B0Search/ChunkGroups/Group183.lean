import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1830
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1831
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1832
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1833
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1834
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1835
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1836
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1837
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1838
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_1839

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_183 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 183 + i)) (500 * (10 * 183 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_1830
  by_cases h1 : i = 1
  · subst i
    exact chunk_1831
  by_cases h2 : i = 2
  · subst i
    exact chunk_1832
  by_cases h3 : i = 3
  · subst i
    exact chunk_1833
  by_cases h4 : i = 4
  · subst i
    exact chunk_1834
  by_cases h5 : i = 5
  · subst i
    exact chunk_1835
  by_cases h6 : i = 6
  · subst i
    exact chunk_1836
  by_cases h7 : i = 7
  · subst i
    exact chunk_1837
  by_cases h8 : i = 8
  · subst i
    exact chunk_1838
  by_cases h9 : i = 9
  · subst i
    exact chunk_1839
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
