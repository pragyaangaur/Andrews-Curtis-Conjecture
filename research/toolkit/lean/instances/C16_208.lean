import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 208 of the cap-16 certificate: slots 212992 .. 214015 -/
theorem chk_208 : chunkCheck 16 T stdSt 212992 1024 = true := by decide +kernel

end Row16
