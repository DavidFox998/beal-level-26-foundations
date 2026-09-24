import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0770
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0771
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0772
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0773
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0774
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0775
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0776
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0777
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0778
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0779

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_077 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 77 + i)) (500 * (10 * 77 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0770
  by_cases h1 : i = 1
  · subst i
    exact chunk_0771
  by_cases h2 : i = 2
  · subst i
    exact chunk_0772
  by_cases h3 : i = 3
  · subst i
    exact chunk_0773
  by_cases h4 : i = 4
  · subst i
    exact chunk_0774
  by_cases h5 : i = 5
  · subst i
    exact chunk_0775
  by_cases h6 : i = 6
  · subst i
    exact chunk_0776
  by_cases h7 : i = 7
  · subst i
    exact chunk_0777
  by_cases h8 : i = 8
  · subst i
    exact chunk_0778
  by_cases h9 : i = 9
  · subst i
    exact chunk_0779
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
