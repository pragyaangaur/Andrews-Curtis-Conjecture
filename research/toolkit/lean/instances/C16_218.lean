import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 218 of the cap-16 certificate: slots 223232 .. 224255 -/
theorem chk_218 : chunkCheck 16 T stdSt 223232 1024 = true := by decide +kernel

end Row16
