import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 417 of the cap-17 certificate: slots 213504 .. 214015 -/
theorem chk_417 : chunkCheck 17 T stdSt 213504 512 = true := by decide +kernel

end Row17
