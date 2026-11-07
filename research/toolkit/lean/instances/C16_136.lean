import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 136 of the cap-16 certificate: slots 139264 .. 140287 -/
theorem chk_136 : chunkCheck 16 T stdSt 139264 1024 = true := by decide +kernel

end Row16
