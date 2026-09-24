import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0640
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0641
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0642
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0643
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0644
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0645
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0646
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0647
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0648
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0649

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_064 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 64 + i)) (500 * (10 * 64 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0640
  by_cases h1 : i = 1
  · subst i
    exact chunk_0641
  by_cases h2 : i = 2
  · subst i
    exact chunk_0642
  by_cases h3 : i = 3
  · subst i
    exact chunk_0643
  by_cases h4 : i = 4
  · subst i
    exact chunk_0644
  by_cases h5 : i = 5
  · subst i
    exact chunk_0645
  by_cases h6 : i = 6
  · subst i
    exact chunk_0646
  by_cases h7 : i = 7
  · subst i
    exact chunk_0647
  by_cases h8 : i = 8
  · subst i
    exact chunk_0648
  by_cases h9 : i = 9
  · subst i
    exact chunk_0649
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
