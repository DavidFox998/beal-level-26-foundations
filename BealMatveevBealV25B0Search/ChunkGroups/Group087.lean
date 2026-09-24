import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0870
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0871
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0872
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0873
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0874
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0875
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0876
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0877
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0878
import BealMatveevBealV25B0Search.Chunks.Chunked10e6_0879

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Ten separate kernel-checked 500-value intervals. -/
theorem group_087 (i : ℕ) (hi : i < 10) :
    checkRange (500 * (10 * 87 + i)) (500 * (10 * 87 + i + 1)) = true := by
  by_cases h0 : i = 0
  · subst i
    exact chunk_0870
  by_cases h1 : i = 1
  · subst i
    exact chunk_0871
  by_cases h2 : i = 2
  · subst i
    exact chunk_0872
  by_cases h3 : i = 3
  · subst i
    exact chunk_0873
  by_cases h4 : i = 4
  · subst i
    exact chunk_0874
  by_cases h5 : i = 5
  · subst i
    exact chunk_0875
  by_cases h6 : i = 6
  · subst i
    exact chunk_0876
  by_cases h7 : i = 7
  · subst i
    exact chunk_0877
  by_cases h8 : i = 8
  · subst i
    exact chunk_0878
  by_cases h9 : i = 9
  · subst i
    exact chunk_0879
  omega

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6
