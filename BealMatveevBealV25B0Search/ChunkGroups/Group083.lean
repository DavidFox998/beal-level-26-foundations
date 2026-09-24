import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0830
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0831
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0832
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0833
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0834
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0835
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0836
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0837
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0838
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0839

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_083 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 83 + i)) (500 * (10 * 83 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0830
  by_cases h1 : i = 1
  · subst i
    exact chunk_0831
  by_cases h2 : i = 2
  · subst i
    exact chunk_0832
  by_cases h3 : i = 3
  · subst i
    exact chunk_0833
  by_cases h4 : i = 4
  · subst i
    exact chunk_0834
  by_cases h5 : i = 5
  · subst i
    exact chunk_0835
  by_cases h6 : i = 6
  · subst i
    exact chunk_0836
  by_cases h7 : i = 7
  · subst i
    exact chunk_0837
  by_cases h8 : i = 8
  · subst i
    exact chunk_0838
  by_cases h9 : i = 9
  · subst i
    exact chunk_0839
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
