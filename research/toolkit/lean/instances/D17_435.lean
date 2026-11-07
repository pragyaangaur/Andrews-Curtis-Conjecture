import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 435 of the cap-17 certificate: slots 222720 .. 223231 -/
theorem chk_435 : chunkCheck 17 T stdSt 222720 512 = true := by decide +kernel

end Row17
