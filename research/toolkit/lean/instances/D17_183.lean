import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 183 of the cap-17 certificate: slots 93696 .. 94207 -/
theorem chk_183 : chunkCheck 17 T stdSt 93696 512 = true := by decide +kernel

end Row17
