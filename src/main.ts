import * as THREE from 'three';
import './style.css';

type Phase = 'День' | 'Сумерки' | 'Ночь' | 'Рассвет';
type SheepState = 'graze' | 'wander' | 'flee' | 'carried';
type DogState = 'patrol' | 'alert' | 'chase' | 'search-visual' | 'search-scent' | 'return';
type RivalState = 'hidden' | 'approach' | 'carry' | 'fight' | 'retreat' | 'escape-warning';
type ShepherdState = 'resting' | 'patrol' | 'investigate' | 'aim' | 'reload';

interface Sheep {
  id: number;
  mesh: THREE.Group;
  velocity: THREE.Vector3;
  alive: boolean;
  turnIn: number;
  state: SheepState;
  carriedBy: 'player' | 'rival' | null;
  bobOffset: number;
  bell: boolean;
}

interface ScentMark {
  position: THREE.Vector3;
  age: number;
  strength: number;
}

interface Obstacle {
  position: THREE.Vector3;
  radius: number;
}

interface Rival {
  mesh: THREE.Group;
  velocity: THREE.Vector3;
  state: RivalState;
  hp: number;
  target?: Sheep;
  carrying?: Sheep;
  exit: THREE.Vector3;
  exitTimer: number;
  attackCooldown: number;
}

const MAP_W = 32;
const MAP_H = 24;
const GOAL = 4;
const START_HEALTH = 6;
const CHANGE_TIME = 3;
const CYCLE_TIME = 120;
const DASH_COOLDOWN = 5;

const ui = {
  phase: required('phase'),
  day: required('day'),
  time: required('time'),
  sheep: required('sheep'),
  lost: required('lost'),
  health: required('health'),
  form: required('form'),
  costume: required('costume'),
  carrying: required('carrying'),
  danger: required('danger'),
  rival: required('rival-status'),
  dash: required('dash-status'),
  hint: required('hint'),
  progress: required('change-progress'),
  sound: requiredButton('sound'),
  overlay: required('overlay'),
  overlayTitle: required('overlay-title'),
  overlayText: required('overlay-text'),
  start: requiredButton('start'),
};

function required(id: string): HTMLElement {
  const element = document.getElementById(id);
  if (!element) throw new Error(`Missing element #${id}`);
  return element;
}

function requiredButton(id: string): HTMLButtonElement {
  const element = required(id);
  if (!(element instanceof HTMLButtonElement)) throw new Error(`#${id} is not a button`);
  return element;
}

class PrototypeGame {
  private readonly scene = new THREE.Scene();
  private readonly camera: THREE.OrthographicCamera;
  private readonly renderer = new THREE.WebGLRenderer({ antialias: true });
  private readonly clock = new THREE.Clock();
  private readonly keys = new Set<string>();
  private readonly sheep: Sheep[] = [];
  private readonly scents: ScentMark[] = [];
  private readonly obstacles: Obstacle[] = [];
  private readonly wolf = this.createWolf();
  private readonly dog = this.createDog();
  private readonly rival: Rival = {
    mesh: this.createRival(),
    velocity: new THREE.Vector3(),
    state: 'hidden',
    hp: 3,
    exit: new THREE.Vector3(-15, 0, 0),
    exitTimer: 0,
    attackCooldown: 0,
  };
  private readonly shepherd = this.createShepherd();
  private readonly sun = new THREE.DirectionalLight(0xffedc7, 2.1);
  private readonly sky = new THREE.HemisphereLight(0xc7e9ff, 0x344223, 1.6);
  private readonly cameraTarget = new THREE.Vector3();
  private readonly playerVelocity = new THREE.Vector3();
  private readonly dogVelocity = new THREE.Vector3();
  private readonly dogFacing = new THREE.Vector3(1, 0, 0);
  private readonly dogLastSeen = new THREE.Vector3();
  private readonly dogPatrolPoints = [
    new THREE.Vector3(-10, 0, -7),
    new THREE.Vector3(0, 0, -7),
    new THREE.Vector3(9, 0, -3),
    new THREE.Vector3(8, 0, 7),
    new THREE.Vector3(-7, 0, 7),
    new THREE.Vector3(-11, 0, 0),
  ];
  private readonly shepherdPatrolPoints = [
    new THREE.Vector3(7.5, 0, -5.2),
    new THREE.Vector3(5, 0, -3),
    new THREE.Vector3(8, 0, 5),
  ];

  private running = false;
  private finished = false;
  private disguised = true;
  private elapsed = 0;
  private changeProgress = 0;
  private score = 0;
  private health = START_HEALTH;
  private maxHealth = START_HEALTH;
  private biteCooldown = 0;
  private actionCooldown = 0;
  private phase: Phase = 'День';
  private previousPhase: Phase = 'День';
  private dayNumber = 1;
  private cycleIndex = 0;
  private guardLevel = 0;
  private lostSheep = 0;
  private perfectPossible = true;
  private playerCarrying?: Sheep;
  private eatProgress = 0;
  private repairProgress = 0;
  private costumeIntegrity = 2;
  private repairKits = 2;
  private bleatCooldown = 0;
  private lureTime = 0;
  private luredSheep?: Sheep;
  private readonly bleatTimes: number[] = [];
  private bellNoiseCooldown = 0;
  private isGrazing = false;
  private playerHeld = 0;
  private playerHeldElapsed = 0;
  private dashCooldown = 0;
  private dashTime = 0;
  private scentTimer = 0;
  private disguiseScentTail = 0;
  private dogState: DogState = 'patrol';
  private dogSuspicion = 0;
  private dogSearchTime = 0;
  private dogBiteWindup = 0;
  private dogConfirmed = false;
  private dogPatrolIndex = 0;
  private shepherdState: ShepherdState = 'resting';
  private shepherdPatrolIndex = 0;
  private shepherdAim = 0;
  private shepherdReload = 0;
  private rivalEntriesThisNight = 0;
  private nextRivalSpawn = 66;
  private paused = false;
  private audioContext?: AudioContext;
  private soundEnabled = true;

  constructor(container: HTMLElement) {
    const aspect = window.innerWidth / window.innerHeight;
    const view = 18;
    this.camera = new THREE.OrthographicCamera(-view * aspect, view * aspect, view, -view, 0.1, 100);
    this.camera.position.set(18, 23, 18);
    this.camera.lookAt(0, 0, 0);

    this.renderer.setPixelRatio(Math.min(devicePixelRatio, 2));
    this.renderer.setSize(window.innerWidth, window.innerHeight);
    this.renderer.shadowMap.enabled = true;
    this.renderer.shadowMap.type = THREE.PCFSoftShadowMap;
    this.renderer.outputColorSpace = THREE.SRGBColorSpace;
    container.appendChild(this.renderer.domElement);

    this.buildWorld();
    this.bindEvents();
    this.reset();
    this.renderer.setAnimationLoop(() => this.frame());
  }

  start(): void {
    this.ensureAudio();
    this.playTone(392, .1, .05);
    window.setTimeout(() => this.playTone(523, .13, .04), 90);
    this.reset();
    this.running = true;
    this.paused = false;
    ui.overlay.classList.add('hidden');
    this.clock.start();
  }

  private reset(): void {
    this.finished = false;
    this.running = false;
    this.elapsed = 0;
    this.score = 0;
    this.health = START_HEALTH;
    this.maxHealth = START_HEALTH;
    this.disguised = true;
    this.changeProgress = 0;
    this.biteCooldown = 0;
    this.actionCooldown = 0;
    this.dayNumber = 1;
    this.cycleIndex = 0;
    this.guardLevel = 0;
    this.lostSheep = 0;
    this.perfectPossible = true;
    this.playerCarrying = undefined;
    this.eatProgress = 0;
    this.repairProgress = 0;
    this.costumeIntegrity = 2;
    this.repairKits = 2;
    this.bleatCooldown = 0;
    this.lureTime = 0;
    this.luredSheep = undefined;
    this.bleatTimes.length = 0;
    this.bellNoiseCooldown = 0;
    this.isGrazing = false;
    this.playerHeld = 0;
    this.playerHeldElapsed = 0;
    this.dashCooldown = 0;
    this.dashTime = 0;
    this.scentTimer = 0;
    this.disguiseScentTail = 0;
    this.scents.length = 0;
    this.playerVelocity.set(0, 0, 0);
    this.wolf.position.set(0, 0, 5);
    this.dog.position.set(-10, 0, -7);
    this.dogVelocity.set(0, 0, 0);
    this.dogFacing.set(1, 0, 0);
    this.dogState = 'patrol';
    this.dogSuspicion = 0;
    this.dogSearchTime = 0;
    this.dogBiteWindup = 0;
    this.dogConfirmed = false;
    this.dogPatrolIndex = 0;
    this.rival.state = 'hidden';
    this.rival.mesh.visible = false;
    this.rival.hp = 3;
    this.rival.target = undefined;
    this.rival.carrying = undefined;
    this.rival.velocity.set(0, 0, 0);
    this.rival.exitTimer = 0;
    this.shepherdState = 'resting';
    this.shepherd.visible = false;
    this.shepherd.position.set(11, 0, -8);
    this.shepherdAim = 0;
    this.shepherdReload = 0;
    this.rivalEntriesThisNight = 0;
    this.nextRivalSpawn = 66;
    this.paused = false;
    this.previousPhase = 'День';
    this.phase = 'День';
    this.setDisguiseVisual();
    this.resetSheep();
    this.updateUi();
  }

  private buildWorld(): void {
    this.scene.background = new THREE.Color(0xaacb8b);
    this.scene.fog = new THREE.Fog(0xaacb8b, 25, 52);

    const ground = new THREE.Mesh(
      new THREE.PlaneGeometry(MAP_W, MAP_H),
      new THREE.MeshStandardMaterial({ color: 0x64814e, roughness: 1 }),
    );
    ground.rotation.x = -Math.PI / 2;
    ground.receiveShadow = true;
    this.scene.add(ground);

    this.sun.position.set(10, 20, 8);
    this.sun.castShadow = true;
    this.sun.shadow.mapSize.set(1024, 1024);
    this.scene.add(this.sun, this.sky);

    this.scene.add(this.wolf, this.dog, this.rival.mesh, this.shepherd);
    for (let i = 0; i < 8; i += 1) {
      const sheep: Sheep = {
        id: i,
        mesh: this.createSheep(i === 0),
        velocity: new THREE.Vector3(),
        alive: true,
        turnIn: 0,
        state: 'graze',
        carriedBy: null,
        bobOffset: random(0, Math.PI * 2),
        bell: i === 0,
      };
      this.sheep.push(sheep);
      this.scene.add(sheep.mesh);
    }

    const fenceMaterial = new THREE.MeshStandardMaterial({ color: 0x765333, roughness: 1 });
    const addFence = (x: number, z: number, sx: number, sz: number) => {
      const fence = new THREE.Mesh(new THREE.BoxGeometry(sx, 0.8, sz), fenceMaterial);
      fence.position.set(x, 0.4, z);
      fence.castShadow = true;
      this.scene.add(fence);
    };
    addFence(0, -MAP_H / 2, MAP_W + 1, 0.28);
    addFence(0, MAP_H / 2, MAP_W + 1, 0.28);
    addFence(-MAP_W / 2, 0, 0.28, MAP_H + 1);
    addFence(MAP_W / 2, 0, 0.28, MAP_H + 1);

    const barn = new THREE.Mesh(
      new THREE.BoxGeometry(5, 3.5, 4),
      new THREE.MeshStandardMaterial({ color: 0x763f32, roughness: .9 }),
    );
    barn.position.set(11, 1.75, -8);
    barn.castShadow = true;
    barn.receiveShadow = true;
    this.scene.add(barn);
    this.obstacles.push({ position: new THREE.Vector3(11, 0, -8), radius: 3.15 });

    const rockMaterial = new THREE.MeshStandardMaterial({ color: 0x657064, roughness: 1 });
    for (const [x, z, radius] of [[-6, -3, 1.25], [4, 5, 1.1], [-9, 7, .9]] as const) {
      const rock = new THREE.Mesh(new THREE.DodecahedronGeometry(radius, 0), rockMaterial);
      rock.position.set(x, radius * .62, z);
      rock.scale.y = .75;
      rock.castShadow = true;
      this.scene.add(rock);
      this.obstacles.push({ position: new THREE.Vector3(x, 0, z), radius: radius + .35 });
    }

    for (let i = 0; i < 34; i += 1) {
      const tuft = new THREE.Mesh(
        new THREE.ConeGeometry(.08 + Math.random() * .08, .35 + Math.random() * .3, 4),
        new THREE.MeshStandardMaterial({ color: i % 3 === 0 ? 0x8ba964 : 0x759653 }),
      );
      tuft.position.set(random(-15, 15), .2, random(-11, 11));
      this.scene.add(tuft);
    }
  }

  private createWolf(): THREE.Group {
    const group = new THREE.Group();
    group.name = 'wolf';
    const dark = new THREE.MeshStandardMaterial({ color: 0x3f4448, roughness: .75 });
    const wool = new THREE.MeshStandardMaterial({ color: 0xe8e1ca, roughness: 1 });
    const body = new THREE.Mesh(new THREE.CapsuleGeometry(.62, 1.05, 5, 10), dark);
    body.rotation.z = Math.PI / 2;
    body.position.y = .78;
    body.castShadow = true;
    const head = new THREE.Mesh(new THREE.ConeGeometry(.55, 1.25, 7), dark);
    head.rotation.z = -Math.PI / 2;
    head.position.set(.95, .95, 0);
    head.castShadow = true;
    const coat = new THREE.Mesh(new THREE.SphereGeometry(.9, 12, 8), wool);
    coat.name = 'coat';
    coat.scale.set(1.15, .85, .85);
    coat.position.y = .82;
    coat.castShadow = true;
    group.add(body, head, coat);
    return group;
  }

  private createSheep(hasBell = false): THREE.Group {
    const group = new THREE.Group();
    const wool = new THREE.MeshStandardMaterial({ color: 0xf3ead4, roughness: 1 });
    const face = new THREE.MeshStandardMaterial({ color: 0x38342f, roughness: 1 });
    const body = new THREE.Mesh(new THREE.SphereGeometry(.68, 10, 8), wool);
    body.scale.set(1.25, .9, .82);
    body.position.y = .72;
    body.castShadow = true;
    const head = new THREE.Mesh(new THREE.BoxGeometry(.42, .5, .45), face);
    head.position.set(.78, .72, 0);
    head.castShadow = true;
    group.add(body, head);
    if (hasBell) {
      const bell = new THREE.Mesh(
        new THREE.SphereGeometry(.12, 8, 6),
        new THREE.MeshStandardMaterial({ color: 0xd6a62d, metalness: .35, roughness: .45 }),
      );
      bell.position.set(.57, .48, 0);
      bell.name = 'bell';
      group.add(bell);
    }
    return group;
  }

  private createDog(): THREE.Group {
    const group = new THREE.Group();
    const material = new THREE.MeshStandardMaterial({ color: 0x7a4f31, roughness: .8 });
    const body = new THREE.Mesh(new THREE.CapsuleGeometry(.58, 1.15, 5, 9), material);
    body.rotation.z = Math.PI / 2;
    body.position.y = .68;
    body.castShadow = true;
    const head = new THREE.Mesh(new THREE.BoxGeometry(.75, .72, .7), material);
    head.position.set(.95, .87, 0);
    head.castShadow = true;
    group.add(body, head);
    return group;
  }

  private createRival(): THREE.Group {
    const group = new THREE.Group();
    group.name = 'rival';
    const material = new THREE.MeshStandardMaterial({ color: 0x232730, roughness: .78 });
    const body = new THREE.Mesh(new THREE.CapsuleGeometry(.58, 1, 5, 9), material);
    body.rotation.z = Math.PI / 2;
    body.position.y = .72;
    body.castShadow = true;
    const head = new THREE.Mesh(new THREE.ConeGeometry(.5, 1.05, 7), material);
    head.rotation.z = -Math.PI / 2;
    head.position.set(.9, .88, 0);
    head.castShadow = true;
    const eyes = new THREE.Mesh(
      new THREE.BoxGeometry(.08, .08, .62),
      new THREE.MeshBasicMaterial({ color: 0xd04d31 }),
    );
    eyes.position.set(1.05, 1.03, 0);
    group.add(body, head, eyes);
    group.visible = false;
    return group;
  }

  private createShepherd(): THREE.Group {
    const group = new THREE.Group();
    group.name = 'shepherd';
    const coat = new THREE.MeshStandardMaterial({ color: 0x34465a, roughness: .85 });
    const skin = new THREE.MeshStandardMaterial({ color: 0xc9936a, roughness: .9 });
    const body = new THREE.Mesh(new THREE.CapsuleGeometry(.38, 1.15, 5, 8), coat);
    body.position.y = 1.05;
    body.castShadow = true;
    const head = new THREE.Mesh(new THREE.SphereGeometry(.34, 10, 8), skin);
    head.position.y = 1.95;
    head.castShadow = true;
    const gun = new THREE.Mesh(
      new THREE.BoxGeometry(1.35, .1, .1),
      new THREE.MeshStandardMaterial({ color: 0x3a2c22, roughness: .7 }),
    );
    gun.name = 'gun';
    gun.position.set(.7, 1.25, 0);
    group.add(body, head, gun);
    group.position.set(11, 0, -8);
    group.visible = false;
    return group;
  }

  private bindEvents(): void {
    window.addEventListener('keydown', (event) => {
      this.keys.add(event.code);
      if (event.code === 'Space') event.preventDefault();
      if (event.code === 'Escape' && !event.repeat) this.togglePause();
      if (event.code === 'KeyR' && this.finished) this.showIntro();
    });
    window.addEventListener('keyup', (event) => this.keys.delete(event.code));
    window.addEventListener('blur', () => {
      this.keys.clear();
      if (this.running) this.togglePause();
    });
    document.addEventListener('visibilitychange', () => {
      if (document.hidden && this.running) this.togglePause();
    });
    window.addEventListener('resize', () => this.resize());
    ui.start.addEventListener('click', () => {
      if (this.paused) this.resume();
      else this.start();
    });
    ui.sound.addEventListener('click', () => {
      this.soundEnabled = !this.soundEnabled;
      ui.sound.textContent = `Звук: ${this.soundEnabled ? 'вкл' : 'выкл'}`;
      ui.sound.setAttribute('aria-pressed', String(this.soundEnabled));
      if (this.soundEnabled) {
        this.ensureAudio();
        this.playTone(520, .08, .035);
      }
    });
  }

  private frame(): void {
    const dt = Math.min(this.clock.getDelta(), .05);
    if (this.running) this.update(dt);
    this.renderer.render(this.scene, this.camera);
  }

  private update(dt: number): void {
    this.elapsed += dt;
    this.biteCooldown = Math.max(0, this.biteCooldown - dt);
    this.actionCooldown = Math.max(0, this.actionCooldown - dt);
    this.dashCooldown = Math.max(0, this.dashCooldown - dt);
    this.bleatCooldown = Math.max(0, this.bleatCooldown - dt);
    this.bellNoiseCooldown = Math.max(0, this.bellNoiseCooldown - dt);
    this.lureTime = Math.max(0, this.lureTime - dt);
    if (this.lureTime <= 0) this.luredSheep = undefined;
    this.dashTime = Math.max(0, this.dashTime - dt);
    this.rival.attackCooldown = Math.max(0, this.rival.attackCooldown - dt);
    this.shepherdReload = Math.max(0, this.shepherdReload - dt);
    if (this.playerHeld > 0) {
      this.playerHeld = Math.max(0, this.playerHeld - dt);
      this.playerHeldElapsed += dt;
      const wantsEscape = this.keys.has('ShiftLeft') || this.keys.has('ShiftRight');
      if (this.playerHeldElapsed >= .15 && wantsEscape && this.dashCooldown <= 0) {
        this.playerHeld = 0;
        this.playerHeldElapsed = 0;
        this.dashCooldown = DASH_COOLDOWN;
        this.dashTime = .18;
        this.playTone(220, .08, .04, 'triangle');
      }
    }
    this.updatePhase();
    if (this.elapsed >= CYCLE_TIME * 3 && this.score < GOAL) {
      this.finish(false, 'Стадо увели', 'Три дня закончились. Пастух усилил охрану и увёл оставшихся овец.');
      return;
    }
    const moved = this.updatePlayer(dt);
    this.updateDisguise(dt, moved);
    this.updateContextActions(dt, moved);
    this.updateScent(dt, moved);
    this.updateRival(dt);
    this.tryBleat();
    this.updateSheep(dt);
    this.updateDog(dt);
    this.updateShepherd(dt);
    this.tryAction();
    this.updateCamera(dt);
    this.updateUi();
  }

  private updatePlayer(dt: number): boolean {
    if (this.playerHeld > 0) {
      this.playerVelocity.multiplyScalar(Math.exp(-20 * dt));
      return false;
    }
    const input = new THREE.Vector3(
      Number(this.keys.has('KeyD') || this.keys.has('ArrowRight')) - Number(this.keys.has('KeyA') || this.keys.has('ArrowLeft')),
      0,
      Number(this.keys.has('KeyS') || this.keys.has('ArrowDown')) - Number(this.keys.has('KeyW') || this.keys.has('ArrowUp')),
    );
    const hasInput = input.lengthSq() > 0;
    if (hasInput) input.normalize();

    if ((this.keys.has('ShiftLeft') || this.keys.has('ShiftRight')) && this.dashCooldown <= 0 && hasInput) {
      if (this.playerCarrying) this.dropPlayerSheep();
      this.dashTime = .18;
      this.dashCooldown = DASH_COOLDOWN;
      this.changeProgress = 0;
      if (this.canSee(this.dog.position, this.dogFacing, this.wolf.position, 8, 130)) {
        this.dogSuspicion = Math.min(100, this.dogSuspicion + (this.disguised ? 35 : 15));
        this.dogLastSeen.copy(this.wolf.position);
      }
      this.playTone(180, .08, .035, 'triangle');
      this.emitNoise(this.wolf.position, 6, this.disguised ? 35 : 20);
    }

    const baseSpeed = this.playerCarrying ? 2.7 : this.disguised ? 2.8 : 3.8;
    const speed = this.dashTime > 0 ? 8.5 : baseSpeed;
    const targetVelocity = input.multiplyScalar(hasInput ? speed : 0);
    const responsiveness = this.dashTime > 0 ? 24 : hasInput ? 12 : 18;
    this.playerVelocity.lerp(targetVelocity, 1 - Math.exp(-responsiveness * dt));
    const previous = this.wolf.position.clone();
    this.wolf.position.addScaledVector(this.playerVelocity, dt);
    this.constrainToMap(this.wolf.position, .85);
    this.resolveObstacles(this.wolf.position, .7, previous);

    if (this.playerVelocity.lengthSq() > .08) {
      this.wolf.rotation.y = Math.atan2(-this.playerVelocity.z, this.playerVelocity.x);
      this.wolf.position.y = Math.sin(this.elapsed * (this.dashTime > 0 ? 22 : 12)) * .045;
    } else {
      this.wolf.position.y = THREE.MathUtils.lerp(this.wolf.position.y, 0, 1 - Math.exp(-12 * dt));
    }
    return this.playerVelocity.lengthSq() > .12;
  }

  private updateDisguise(dt: number, moved: boolean): void {
    if (!this.keys.has('KeyF')) {
      this.changeProgress = 0;
      return;
    }
    if (this.playerCarrying) {
      this.changeProgress = 0;
      ui.hint.textContent = 'Сначала бросьте или съешьте овцу';
      return;
    }
    if (moved) {
      this.changeProgress = 0;
      ui.hint.textContent = 'Чтобы переодеться, стойте неподвижно';
      return;
    }
    this.changeProgress += dt;
    if (this.changeProgress >= CHANGE_TIME) {
      this.disguised = !this.disguised;
      this.changeProgress = 0;
      this.keys.delete('KeyF');
      this.setDisguiseVisual();
      this.playTone(this.disguised ? 620 : 310, .12, .035);
    }
  }

  private setDisguiseVisual(): void {
    const coat = this.wolf.getObjectByName('coat');
    if (coat) {
      coat.visible = this.disguised;
      if (coat instanceof THREE.Mesh && coat.material instanceof THREE.MeshStandardMaterial) {
        const colors = [0x7e776a, 0xc5beaa, 0xe8e1ca];
        coat.material.color.setHex(colors[this.costumeIntegrity]);
      }
    }
  }

  private updateSheep(dt: number): void {
    for (const sheep of this.sheep) {
      if (!sheep.alive) continue;
      if (sheep.carriedBy === 'player') {
        sheep.state = 'carried';
        const forward = new THREE.Vector3(Math.cos(this.wolf.rotation.y), 0, -Math.sin(this.wolf.rotation.y));
        sheep.mesh.position.copy(this.wolf.position).addScaledVector(forward, .92);
        sheep.mesh.position.y = .42;
        sheep.mesh.rotation.y = this.wolf.rotation.y;
        continue;
      }
      if (sheep.carriedBy === 'rival') {
        sheep.state = 'carried';
        sheep.mesh.position.copy(this.rival.mesh.position).add(new THREE.Vector3(.1, .55, -.65));
        sheep.mesh.rotation.y = this.rival.mesh.rotation.y;
        continue;
      }

      sheep.turnIn -= dt;
      const wolfDistance = sheep.mesh.position.distanceTo(this.wolf.position);
      const rivalDistance = this.rival.mesh.visible ? sheep.mesh.position.distanceTo(this.rival.mesh.position) : Infinity;
      const desired = new THREE.Vector3();
      const separation = new THREE.Vector3();
      const cohesion = new THREE.Vector3();
      const alignment = new THREE.Vector3();
      let neighbors = 0;

      for (const other of this.sheep) {
        if (other === sheep || !other.alive || other.carriedBy) continue;
        const distance = sheep.mesh.position.distanceTo(other.mesh.position);
        if (distance < 4.2) {
          cohesion.add(other.mesh.position);
          alignment.add(other.velocity);
          neighbors += 1;
          if (distance < 1.35 && distance > .001) {
            separation.add(sheep.mesh.position.clone().sub(other.mesh.position).multiplyScalar(1 / distance));
          }
        }
      }

      const threatened = (!this.disguised && wolfDistance < 6.2) || rivalDistance < 5.2;
      if (threatened) {
        sheep.state = 'flee';
        if (sheep.bell && this.bellNoiseCooldown <= 0) {
          this.bellNoiseCooldown = 3;
          this.emitNoise(sheep.mesh.position, 7, 24, true);
          this.playTone(880, .08, .025, 'triangle');
        }
        if (!this.disguised && wolfDistance < 6.2) {
          desired.add(sheep.mesh.position.clone().sub(this.wolf.position).setY(0).multiplyScalar(1 / Math.max(.4, wolfDistance)));
        }
        if (rivalDistance < 5.2) {
          desired.add(sheep.mesh.position.clone().sub(this.rival.mesh.position).setY(0).multiplyScalar(1 / Math.max(.4, rivalDistance)));
        }
        desired.normalize().multiplyScalar(2.65);
        sheep.turnIn = random(.5, 1.1);
      } else if (sheep === this.luredSheep && this.lureTime > 0 && this.disguised) {
        sheep.state = wolfDistance > 1.05 ? 'wander' : 'graze';
        if (wolfDistance > 1.05) {
          desired.copy(this.wolf.position).sub(sheep.mesh.position).setY(0).normalize().multiplyScalar(1.05);
        }
        sheep.turnIn = .4;
      } else {
        if (sheep.turnIn <= 0) {
          sheep.state = Math.random() < .42 ? 'graze' : 'wander';
          sheep.turnIn = sheep.state === 'graze' ? random(1.1, 2.6) : random(1.5, 4.2);
        }
        if (sheep.state === 'wander') {
          const angle = sheep.mesh.rotation.y + random(-1.1, 1.1);
          desired.set(Math.cos(angle), 0, -Math.sin(angle)).multiplyScalar(.75);
        }
        if (neighbors > 0) {
          cohesion.multiplyScalar(1 / neighbors).sub(sheep.mesh.position).setY(0).multiplyScalar(.12);
          alignment.multiplyScalar(1 / neighbors).multiplyScalar(.18);
          desired.add(cohesion).add(alignment);
        }
      }

      desired.add(separation.multiplyScalar(1.5));
      desired.add(this.avoidObstacles(sheep.mesh.position, 2.2).multiplyScalar(1.3));
      const maxSpeed = sheep.state === 'flee' ? 2.65 : sheep.state === 'graze' ? .08 : .9;
      if (desired.lengthSq() > maxSpeed * maxSpeed) desired.setLength(maxSpeed);
      sheep.velocity.lerp(desired, 1 - Math.exp(-(sheep.state === 'flee' ? 8 : 3.5) * dt));

      const previous = sheep.mesh.position.clone();
      sheep.mesh.position.addScaledVector(sheep.velocity, dt);
      this.constrainToMap(sheep.mesh.position, 1.1);
      this.resolveObstacles(sheep.mesh.position, .62, previous);
      if (sheep.velocity.lengthSq() > .015) sheep.mesh.rotation.y = Math.atan2(-sheep.velocity.z, sheep.velocity.x);
      sheep.mesh.position.y = Math.abs(Math.sin(this.elapsed * (sheep.state === 'flee' ? 12 : 6) + sheep.bobOffset)) * (sheep.state === 'flee' ? .1 : .025);
    }
  }

  private updateDog(dt: number): void {
    const night = this.phase === 'Ночь' || this.phase === 'Сумерки';
    const viewRadius = (night ? 5.5 : 7) + this.guardLevel * .25;
    const seesPlayer = this.canSee(this.dog.position, this.dogFacing, this.wolf.position, viewRadius, 110);
    const distance = this.dog.position.distanceTo(this.wolf.position);
    const rivalThreat = this.rival.mesh.visible && this.rival.carrying
      && this.canSee(this.dog.position, this.dogFacing, this.rival.mesh.position, 9, 130);

    if (seesPlayer) {
      if (!this.disguised) {
        this.dogSuspicion = Math.min(100, this.dogSuspicion + dt * 260);
        this.dogLastSeen.copy(this.wolf.position);
        this.dogConfirmed = true;
      } else {
        const damageRate = (this.costumeIntegrity === 0 ? 60 : this.costumeIntegrity === 1 ? 20 : 0)
          * (1 + this.guardLevel * .1);
        const closeInspection = distance < 2.8 ? damageRate : 0;
        const grazingRelief = this.isGrazing && !this.dogConfirmed ? 14 : 0;
        this.dogSuspicion = THREE.MathUtils.clamp(this.dogSuspicion + (closeInspection - grazingRelief) * dt, 0, 100);
        if (this.costumeIntegrity === 0 && this.dogSuspicion >= 100) this.dogConfirmed = true;
      }
    } else if (this.dogState !== 'chase') {
      this.dogSuspicion = Math.max(0, this.dogSuspicion - dt * 10);
    }

    if (rivalThreat) {
      this.moveDogToward(this.rival.mesh.position, 4.35, dt);
      if (this.dog.position.distanceTo(this.rival.mesh.position) < 1.35) {
        this.dropRivalSheep();
        this.rival.state = 'retreat';
        this.rival.hp -= 1;
        this.playTone(125, .18, .065, 'sawtooth');
      }
      return;
    }

    if (this.dogSuspicion >= 100 && seesPlayer && (!this.disguised || this.dogConfirmed)) this.dogState = 'chase';
    else if (this.dogSuspicion >= 55 && this.dogState === 'patrol') this.dogState = 'alert';

    switch (this.dogState) {
      case 'patrol': {
        const target = this.dogPatrolPoints[this.dogPatrolIndex];
        this.moveDogToward(target, (night ? 2.15 : 1.6) + this.guardLevel * .08, dt);
        if (this.dog.position.distanceTo(target) < .7) {
          this.dogPatrolIndex = (this.dogPatrolIndex + 1) % this.dogPatrolPoints.length;
        }
        break;
      }
      case 'alert':
        if (seesPlayer) this.moveDogToward(this.wolf.position, 2.1, dt);
        else {
          this.dogSearchTime += dt;
          this.moveDogToward(this.dogLastSeen, 1.8, dt);
          if (this.dogSuspicion <= 20 || this.dogSearchTime > 3) {
            this.dogState = 'return';
            this.dogSearchTime = 0;
          }
        }
        break;
      case 'chase':
        if (seesPlayer && (!this.disguised || this.dogConfirmed)) {
          this.dogLastSeen.copy(this.wolf.position);
          const intercept = this.wolf.position.clone().addScaledVector(this.playerVelocity, Math.min(.55, distance / 12));
          this.moveDogToward(intercept, 4.2 + this.guardLevel * .12, dt);
        } else {
          this.dogState = 'search-visual';
          this.dogSearchTime = 0;
          this.dogBiteWindup = 0;
        }
        break;
      case 'search-visual':
        this.dogSearchTime += dt;
        this.moveDogToward(this.dogLastSeen, 2.5, dt);
        if (seesPlayer && (!this.disguised || this.dogConfirmed)) this.dogState = 'chase';
        else if (this.dog.position.distanceTo(this.dogLastSeen) < .75 || this.dogSearchTime > 4) {
          this.dogState = 'search-scent';
          this.dogSearchTime = 0;
        }
        break;
      case 'search-scent': {
        this.dogSearchTime += dt;
        const scent = this.findLocalScent();
        if (scent) {
          this.moveDogToward(scent.position, 2.25, dt);
          this.dogLastSeen.copy(scent.position);
        } else {
          this.dogVelocity.multiplyScalar(Math.exp(-5 * dt));
          this.dog.rotation.y += dt * 1.4;
        }
        if (seesPlayer && (!this.disguised || this.dogConfirmed)) this.dogState = 'chase';
        else if (this.dogSearchTime > 6 || (this.scents.length === 0 && this.dogSearchTime > 2)) {
          this.dogState = 'return';
          this.dogConfirmed = false;
          this.dogSuspicion = Math.min(this.dogSuspicion, 15);
        }
        break;
      }
      case 'return': {
        const target = this.dogPatrolPoints[this.dogPatrolIndex];
        this.moveDogToward(target, 1.9, dt);
        if (this.dog.position.distanceTo(target) < .8) this.dogState = 'patrol';
        break;
      }
    }

    const canBite = this.dogState === 'chase' && distance < 1.45 && this.biteCooldown <= 0
      && this.playerHeld <= 0 && this.dashTime <= 0;
    this.dogBiteWindup = canBite ? this.dogBiteWindup + dt : 0;
    if (this.dogBiteWindup >= .3) {
      this.dogBiteWindup = 0;
      const toWolf = this.wolf.position.clone().sub(this.dog.position).setY(0);
      this.maxHealth = Math.max(0, this.maxHealth - 1);
      this.health = Math.min(this.health - 1, this.maxHealth);
      if (this.disguised) {
        this.costumeIntegrity = Math.max(0, this.costumeIntegrity - 1);
        this.setDisguiseVisual();
      }
      if (this.playerCarrying) this.dropPlayerSheep();
      this.biteCooldown = 1.4;
      const shepherdCanHold = this.shepherd.visible && this.shepherd.position.distanceTo(this.dog.position) <= 6;
      if (shepherdCanHold) {
        this.playerHeld = 1.2;
        this.playerHeldElapsed = 0;
      }
      this.playTone(105, .2, .075, 'sawtooth');
      if (toWolf.lengthSq() > .001) this.wolf.position.addScaledVector(toWolf.normalize(), 1.35);
      if (this.health <= 0) this.finish(false, 'Пёс оставил последнюю рану', 'Пёс видит только то, что действительно наблюдал, но на прямой он быстрее. Разрывайте видимость и уводите его на старый запах.');
    }
  }

  private updateScent(dt: number, moved: boolean): void {
    for (let i = this.scents.length - 1; i >= 0; i -= 1) {
      this.scents[i].age += dt;
      if (this.scents[i].age >= 10) this.scents.splice(i, 1);
    }
    if (!this.disguised) this.disguiseScentTail = 2;
    else this.disguiseScentTail = Math.max(0, this.disguiseScentTail - dt);
    this.scentTimer -= dt;
    const leavesScent = !this.disguised || this.disguiseScentTail > 0;
    if (leavesScent && this.scentTimer <= 0) {
      this.scents.push({
        position: this.wolf.position.clone().setY(0),
        age: 0,
        strength: this.playerCarrying ? 1.35 : !this.disguised ? (moved ? 1 : .75) : .3,
      });
      this.scentTimer = moved ? .35 : 1;
      if (this.scents.length > 192) this.scents.splice(0, this.scents.length - 192);
    }
  }

  private updateContextActions(dt: number, moved: boolean): void {
    this.isGrazing = this.keys.has('KeyG') && this.disguised && !moved && !this.playerCarrying && this.playerHeld <= 0;
    if (this.isGrazing && !this.dogConfirmed) {
      this.dogSuspicion = Math.max(0, this.dogSuspicion - dt * 8);
    }

    if (!this.keys.has('KeyE') || moved || this.playerHeld > 0) {
      this.eatProgress = 0;
      this.repairProgress = 0;
      return;
    }

    if (this.playerCarrying && !this.disguised) {
      this.eatProgress += dt;
      this.repairProgress = 0;
      if (this.eatProgress >= 1.6) {
        this.eatProgress = 0;
        this.keys.delete('KeyE');
        this.completeEating();
      }
      return;
    }

    const nearBarn = this.wolf.position.distanceTo(new THREE.Vector3(11, 0, -8)) < 4.5;
    if (nearBarn && this.disguised && this.costumeIntegrity < 2 && this.repairKits > 0) {
      this.repairProgress += dt;
      this.eatProgress = 0;
      if (this.repairProgress >= 2) {
        this.repairProgress = 0;
        this.repairKits -= 1;
        this.costumeIntegrity += 1;
        this.keys.delete('KeyE');
        this.setDisguiseVisual();
        this.playTone(560, .15, .035, 'triangle');
      }
      return;
    }

    this.eatProgress = 0;
    this.repairProgress = 0;
  }

  private updateRival(dt: number): void {
    const cycle = this.elapsed % CYCLE_TIME;
    const isNight = this.phase === 'Ночь';
    const entryBudget = this.dayNumber >= 3 ? 2 : 1;
    if (isNight && cycle >= this.nextRivalSpawn && cycle < 101
      && this.rival.state === 'hidden' && this.rivalEntriesThisNight < entryBudget) {
      this.spawnRival();
    }
    if ((this.phase === 'Рассвет' || this.phase === 'День') && this.rival.state !== 'hidden') {
      this.dropRivalSheep();
      this.rival.state = 'retreat';
    }
    if (this.rival.state === 'hidden') return;

    const distanceToPlayer = this.rival.mesh.position.distanceTo(this.wolf.position);
    if (distanceToPlayer < 1.35 && this.rival.attackCooldown <= 0
      && this.rival.state !== 'retreat' && this.dashTime <= 0) {
      this.health -= 1;
      if (this.disguised) {
        this.costumeIntegrity = Math.max(0, this.costumeIntegrity - 1);
        this.setDisguiseVisual();
      }
      if (this.playerCarrying) this.dropPlayerSheep();
      this.rival.attackCooldown = 1.25;
      this.playTone(150, .12, .05, 'square');
      const knockback = this.wolf.position.clone().sub(this.rival.mesh.position).setY(0);
      if (knockback.lengthSq() > .001) this.wolf.position.addScaledVector(knockback.normalize(), 1);
      if (this.health <= 0) this.finish(false, 'Соперник выиграл схватку', 'Обычные раны можно лечить едой, но прямой бой опасен. Перехватывайте носителя сбоку и используйте рывок.');
    }

    if (this.rival.state === 'retreat') {
      this.moveRivalToward(this.rival.exit, 3.7, dt);
      if (this.rival.mesh.position.distanceTo(this.rival.exit) < .55) this.hideRival();
      return;
    }

    if (!this.rival.target || !this.rival.target.alive || this.rival.target.carriedBy) {
      this.rival.target = this.chooseRivalTarget();
    }
    if (!this.rival.target) {
      this.rival.state = 'retreat';
      return;
    }

    if (this.rival.state === 'approach' || this.rival.state === 'fight') {
      this.moveRivalToward(this.rival.target.mesh.position, 3.35, dt);
      if (this.rival.mesh.position.distanceTo(this.rival.target.mesh.position) < 1.15) {
        this.rival.carrying = this.rival.target;
        this.rival.target.carriedBy = 'rival';
        this.rival.target.state = 'carried';
        this.rival.exit = this.nearestExit(this.rival.mesh.position);
        this.rival.state = 'carry';
        this.playTone(210, .18, .045, 'triangle');
        this.emitNoise(this.rival.mesh.position, 4, 18, true, true);
      }
    } else if (this.rival.state === 'carry' || this.rival.state === 'escape-warning') {
      this.moveRivalToward(this.rival.exit, 2.65, dt);
      const exitDistance = this.rival.mesh.position.distanceTo(this.rival.exit);
      if (exitDistance < 1.8) this.rival.state = 'escape-warning';
      if (this.rival.state === 'escape-warning' && exitDistance < .55) {
        this.rival.exitTimer += dt;
        if (this.rival.exitTimer >= 1.2 && this.rival.carrying) {
          this.rival.carrying.alive = false;
          this.rival.carrying.carriedBy = null;
          this.rival.carrying.mesh.visible = false;
          this.rival.carrying = undefined;
          this.lostSheep += 1;
          this.perfectPossible = false;
          this.playTone(92, .4, .06, 'sawtooth');
          this.hideRival();
          this.checkNoSheepResult();
        }
      } else {
        this.rival.exitTimer = 0;
      }
    }
  }

  private updateShepherd(dt: number): void {
    const cycle = this.elapsed % CYCLE_TIME;
    const shouldBeActive = this.phase === 'Ночь'
      || (this.phase === 'День' && cycle >= 35 - this.guardLevel * 2 && cycle <= 48 + this.guardLevel);
    if (!shouldBeActive) {
      this.shepherdState = 'resting';
      this.shepherd.visible = false;
      this.shepherdAim = 0;
      return;
    }
    if (this.shepherdState === 'resting') {
      this.shepherdState = 'patrol';
      this.shepherd.visible = true;
      this.shepherd.position.set(7.5, 0, -5.2);
    }

    const facing = new THREE.Vector3(Math.cos(this.shepherd.rotation.y), 0, -Math.sin(this.shepherd.rotation.y));
    const seesPlayer = (!this.disguised || (this.playerHeld > 0 && this.dogConfirmed))
      && this.canSee(this.shepherd.position, facing, this.wolf.position, 8, 100);
    if (seesPlayer && this.shepherdReload <= 0) {
      this.shepherdState = 'aim';
      this.shepherdAim += dt;
      const direction = this.wolf.position.clone().sub(this.shepherd.position).setY(0).normalize();
      this.shepherd.rotation.y = Math.atan2(-direction.z, direction.x);
      const aimDuration = this.playerHeld > 0 ? .45 : .9;
      if (this.shepherdAim >= aimDuration) {
        this.shepherdAim = 0;
        this.shepherdReload = Math.max(1.9, 2.5 - this.guardLevel * .15);
        this.shepherdState = 'reload';
        this.playTone(70, .28, .09, 'square');
        if (this.dashTime > 0) {
          this.playTone(310, .09, .035, 'triangle');
        } else if (this.canSee(this.shepherd.position, direction, this.wolf.position, 8.4, 16)) {
          this.finish(false, 'Пастух попал в цель', 'Прицеливание заметно заранее. Разрывайте линию видимости за крупным укрытием или уходите рывком в сторону.');
        }
      }
      return;
    }

    this.shepherdAim = Math.max(0, this.shepherdAim - dt * 2.5);
    if (this.shepherdReload > 0) this.shepherdState = 'reload';
    else if (this.dogState === 'chase' || this.dogState === 'alert') {
      this.shepherdState = 'investigate';
      this.moveShepherdToward(this.dogLastSeen, 1.8, dt);
    } else {
      this.shepherdState = 'patrol';
      const target = this.shepherdPatrolPoints[this.shepherdPatrolIndex];
      this.moveShepherdToward(target, 1.35, dt);
      if (this.shepherd.position.distanceTo(target) < .6) {
        this.shepherdPatrolIndex = (this.shepherdPatrolIndex + 1) % this.shepherdPatrolPoints.length;
      }
    }
  }

  private tryBleat(): void {
    if (!this.keys.has('KeyQ') || this.bleatCooldown > 0 || this.playerHeld > 0 || !this.disguised) return;
    this.keys.delete('KeyQ');
    this.bleatCooldown = 6;
    this.bleatTimes.push(this.elapsed);
    while (this.bleatTimes.length > 0 && this.elapsed - this.bleatTimes[0] > 15) this.bleatTimes.shift();

    let target: Sheep | undefined;
    let targetDistance = 4.5;
    for (const sheep of this.sheep) {
      if (!sheep.alive || sheep.carriedBy || sheep.state === 'flee') continue;
      const distance = sheep.mesh.position.distanceTo(this.wolf.position);
      if (distance < targetDistance) {
        target = sheep;
        targetDistance = distance;
      }
    }
    this.luredSheep = target;
    this.lureTime = target ? 2.5 : 0;
    const repeated = this.bleatTimes.length >= 3;
    if (repeated) this.emitNoise(this.wolf.position, 6, 38, true);
    this.playTone(target ? 510 : 390, .16, .035, 'triangle');
  }

  private tryAction(): void {
    if (!this.keys.has('Space') || this.actionCooldown > 0 || this.disguised) return;
    if (this.playerCarrying) {
      this.dropPlayerSheep();
      this.actionCooldown = .3;
      this.keys.delete('Space');
      return;
    }
    if (this.rival.mesh.visible && this.rival.mesh.position.distanceTo(this.wolf.position) < 1.85) {
      this.rival.hp -= 1;
      this.rival.state = this.rival.hp <= 0 ? 'retreat' : 'fight';
      this.dropRivalSheep();
      const push = this.rival.mesh.position.clone().sub(this.wolf.position).setY(0);
      if (push.lengthSq() > .001) this.rival.mesh.position.addScaledVector(push.normalize(), 1.2);
      this.actionCooldown = .55;
      this.keys.delete('Space');
      this.playTone(165, .1, .055, 'square');
      this.emitNoise(this.wolf.position, 6, 35, true, true);
      return;
    }
    let nearest: Sheep | undefined;
    let nearestDistance = 1.65;
    for (const sheep of this.sheep) {
      if (!sheep.alive || sheep.carriedBy) continue;
      const distance = sheep.mesh.position.distanceTo(this.wolf.position);
      if (distance < nearestDistance) {
        nearest = sheep;
        nearestDistance = distance;
      }
    }
    if (!nearest) return;
    this.playerCarrying = nearest;
    nearest.carriedBy = 'player';
    nearest.state = 'carried';
    nearest.velocity.set(0, 0, 0);
    this.emitNoise(this.wolf.position, 4, 25, true, true);
    this.playTone(230, .11, .04, 'triangle');
    this.actionCooldown = .45;
    this.keys.delete('Space');
  }

  private completeEating(): void {
    const sheep = this.playerCarrying;
    if (!sheep) return;
    sheep.alive = false;
    sheep.carriedBy = null;
    sheep.mesh.visible = false;
    this.playerCarrying = undefined;
    this.score += 1;
    this.health = Math.min(this.maxHealth, this.health + 2);
    this.emitNoise(this.wolf.position, 5, 45, true, true);
    this.playTone(245 + this.score * 55, .16, .06);
    this.actionCooldown = 1.1;
    if (this.score >= GOAL) {
      const title = this.perfectPossible ? 'Идеальная охота' : 'Охота завершена';
      const text = this.perfectPossible
        ? 'Вы лично добыли нужное количество овец и не позволили сопернику унести ни одной.'
        : `Вы выполнили квоту, но соперник унёс овец: ${this.lostSheep}. Идеальный исход уже был потерян.`;
      this.finish(true, title, text);
    } else {
      this.checkNoSheepResult();
    }
  }

  private dropPlayerSheep(): void {
    const sheep = this.playerCarrying;
    if (!sheep) return;
    sheep.carriedBy = null;
    sheep.state = 'flee';
    sheep.mesh.visible = true;
    const forward = new THREE.Vector3(Math.cos(this.wolf.rotation.y), 0, -Math.sin(this.wolf.rotation.y));
    sheep.mesh.position.copy(this.wolf.position).addScaledVector(forward, 1.1).setY(0);
    sheep.velocity.copy(forward).multiplyScalar(1.8);
    sheep.turnIn = .65;
    this.playerCarrying = undefined;
    this.eatProgress = 0;
  }

  private spawnRival(): void {
    const entrances = [
      new THREE.Vector3(-15, 0, -7),
      new THREE.Vector3(-15, 0, 7),
      new THREE.Vector3(15, 0, 6),
    ];
    const safe = entrances.filter((point) => point.distanceTo(this.wolf.position) >= 6);
    const spawn = (safe.length > 0 ? safe : entrances)[Math.floor(Math.random() * (safe.length || entrances.length))];
    this.rival.mesh.position.copy(spawn);
    this.rival.mesh.visible = true;
    this.rival.state = 'approach';
    this.rival.hp = 3 + Math.floor(this.guardLevel / 2);
    this.rival.exitTimer = 0;
    this.rivalEntriesThisNight += 1;
    this.rival.target = this.chooseRivalTarget();
    this.rival.exit = this.nearestExit(spawn);
    this.playTone(145, .45, .035, 'triangle');
  }

  private hideRival(): void {
    this.dropRivalSheep();
    this.rival.mesh.visible = false;
    this.rival.state = 'hidden';
    this.rival.target = undefined;
    this.rival.velocity.set(0, 0, 0);
    this.rival.exitTimer = 0;
    this.nextRivalSpawn = Math.min(101, (this.elapsed % CYCLE_TIME) + 9);
  }

  private dropRivalSheep(): void {
    const carried = this.rival.carrying;
    if (!carried) return;
    carried.carriedBy = null;
    carried.state = 'flee';
    carried.mesh.visible = true;
    carried.mesh.position.copy(this.rival.mesh.position).add(new THREE.Vector3(0, 0, .8));
    const away = carried.mesh.position.clone().sub(this.rival.mesh.position).setY(0);
    carried.velocity.copy(away.lengthSq() > .001 ? away.normalize().multiplyScalar(2.2) : new THREE.Vector3(0, 0, 2.2));
    carried.turnIn = .7;
    this.rival.carrying = undefined;
    this.rival.exitTimer = 0;
  }

  private chooseRivalTarget(): Sheep | undefined {
    let best: Sheep | undefined;
    let bestScore = Infinity;
    for (const sheep of this.sheep) {
      if (!sheep.alive || sheep.carriedBy) continue;
      const dogRisk = Math.max(0, 6 - sheep.mesh.position.distanceTo(this.dog.position)) * 1.8;
      const playerCompetition = Math.max(0, 3 - sheep.mesh.position.distanceTo(this.wolf.position));
      const score = sheep.mesh.position.distanceTo(this.rival.mesh.position) + dogRisk + playerCompetition;
      if (score < bestScore) {
        best = sheep;
        bestScore = score;
      }
    }
    return best;
  }

  private nearestExit(position: THREE.Vector3): THREE.Vector3 {
    const exits = [
      new THREE.Vector3(-15.3, 0, -7),
      new THREE.Vector3(-15.3, 0, 7),
      new THREE.Vector3(15.3, 0, 6),
      new THREE.Vector3(0, 0, -11.3),
    ];
    return exits.reduce((best, point) => point.distanceTo(position) < best.distanceTo(position) ? point : best).clone();
  }

  private moveDogToward(target: THREE.Vector3, speed: number, dt: number): void {
    const direction = target.clone().sub(this.dog.position).setY(0);
    if (direction.lengthSq() > .02) direction.normalize().multiplyScalar(speed);
    direction.add(this.avoidObstacles(this.dog.position, 2.5).multiplyScalar(speed));
    if (direction.lengthSq() > speed * speed) direction.setLength(speed);
    this.dogVelocity.lerp(direction, 1 - Math.exp(-8 * dt));
    const previous = this.dog.position.clone();
    this.dog.position.addScaledVector(this.dogVelocity, dt);
    this.constrainToMap(this.dog.position, .8);
    this.resolveObstacles(this.dog.position, .7, previous);
    if (this.dogVelocity.lengthSq() > .04) {
      this.dogFacing.copy(this.dogVelocity).normalize();
      this.dog.rotation.y = Math.atan2(-this.dogFacing.z, this.dogFacing.x);
      this.dog.position.y = Math.abs(Math.sin(this.elapsed * 13)) * .05;
    }
  }

  private moveRivalToward(target: THREE.Vector3, speed: number, dt: number): void {
    const direction = target.clone().sub(this.rival.mesh.position).setY(0);
    if (direction.lengthSq() > .02) direction.normalize().multiplyScalar(speed);
    direction.add(this.avoidObstacles(this.rival.mesh.position, 2.2).multiplyScalar(speed));
    if (direction.lengthSq() > speed * speed) direction.setLength(speed);
    this.rival.velocity.lerp(direction, 1 - Math.exp(-8 * dt));
    const previous = this.rival.mesh.position.clone();
    this.rival.mesh.position.addScaledVector(this.rival.velocity, dt);
    this.constrainToMap(this.rival.mesh.position, .45);
    this.resolveObstacles(this.rival.mesh.position, .65, previous);
    if (this.rival.velocity.lengthSq() > .04) {
      this.rival.mesh.rotation.y = Math.atan2(-this.rival.velocity.z, this.rival.velocity.x);
      this.rival.mesh.position.y = Math.abs(Math.sin(this.elapsed * 12 + 1.7)) * .055;
    }
  }

  private moveShepherdToward(target: THREE.Vector3, speed: number, dt: number): void {
    const direction = target.clone().sub(this.shepherd.position).setY(0);
    if (direction.lengthSq() < .02) return;
    direction.normalize();
    const previous = this.shepherd.position.clone();
    this.shepherd.position.addScaledVector(direction, speed * dt);
    this.constrainToMap(this.shepherd.position, .8);
    this.resolveObstacles(this.shepherd.position, .55, previous);
    this.shepherd.rotation.y = Math.atan2(-direction.z, direction.x);
    this.shepherd.position.y = Math.abs(Math.sin(this.elapsed * 8)) * .025;
  }

  private constrainToMap(position: THREE.Vector3, margin: number): void {
    position.x = THREE.MathUtils.clamp(position.x, -MAP_W / 2 + margin, MAP_W / 2 - margin);
    position.z = THREE.MathUtils.clamp(position.z, -MAP_H / 2 + margin, MAP_H / 2 - margin);
  }

  private resolveObstacles(position: THREE.Vector3, radius: number, previous: THREE.Vector3): void {
    for (const obstacle of this.obstacles) {
      const offset = position.clone().sub(obstacle.position).setY(0);
      const minimum = obstacle.radius + radius;
      if (offset.lengthSq() < minimum * minimum) {
        if (offset.lengthSq() < .0001) position.copy(previous);
        else position.copy(obstacle.position).add(offset.setLength(minimum));
      }
    }
  }

  private avoidObstacles(position: THREE.Vector3, influence: number): THREE.Vector3 {
    const force = new THREE.Vector3();
    for (const obstacle of this.obstacles) {
      const offset = position.clone().sub(obstacle.position).setY(0);
      const distance = offset.length();
      const range = obstacle.radius + influence;
      if (distance < range && distance > .001) force.add(offset.normalize().multiplyScalar((range - distance) / range));
    }
    return force;
  }

  private canSee(origin: THREE.Vector3, facing: THREE.Vector3, target: THREE.Vector3, radius: number, angleDegrees: number): boolean {
    const toTarget = target.clone().sub(origin).setY(0);
    const distance = toTarget.length();
    if (distance > radius) return false;
    if (distance > .8) {
      const direction = toTarget.clone().normalize();
      const normalizedFacing = facing.lengthSq() > .001 ? facing.clone().normalize() : new THREE.Vector3(1, 0, 0);
      if (normalizedFacing.dot(direction) < Math.cos(THREE.MathUtils.degToRad(angleDegrees / 2))) return false;
    }
    for (const obstacle of this.obstacles) {
      if (distancePointToSegment(obstacle.position, origin, target) < obstacle.radius * .82) return false;
    }
    return true;
  }

  private findLocalScent(): ScentMark | undefined {
    let best: ScentMark | undefined;
    let bestValue = -Infinity;
    for (const mark of this.scents) {
      const freshness = Math.max(0, 1 - mark.age / 10);
      const strength = mark.strength * freshness * freshness;
      const perception = 2.4 * Math.sqrt(Math.min(1, strength));
      const distance = mark.position.distanceTo(this.dog.position);
      if (distance <= perception && strength - distance * .08 > bestValue) {
        best = mark;
        bestValue = strength - distance * .08;
      }
    }
    return best;
  }

  private emitNoise(
    position: THREE.Vector3,
    radius: number,
    suspicion: number,
    investigate = true,
    scareSheep = false,
  ): void {
    if (this.dog.position.distanceTo(position) <= radius) {
      this.dogLastSeen.copy(position);
      this.dogSuspicion = Math.min(100, this.dogSuspicion + suspicion);
      if (investigate && (this.dogState === 'patrol' || this.dogState === 'return')) {
        this.dogState = 'alert';
        this.dogSearchTime = 0;
      }
    }
    if (investigate && this.shepherd.visible && this.shepherd.position.distanceTo(position) <= radius + 2
      && this.shepherdState !== 'aim') {
      this.shepherdState = 'investigate';
    }
    if (scareSheep) {
      for (const sheep of this.sheep) {
        if (!sheep.alive || sheep.carriedBy) continue;
        const distance = sheep.mesh.position.distanceTo(position);
        if (distance > radius) continue;
        sheep.state = 'flee';
        sheep.turnIn = Math.max(sheep.turnIn, 1.2);
        const away = sheep.mesh.position.clone().sub(position).setY(0);
        if (away.lengthSq() > .001) sheep.velocity.addScaledVector(away.normalize(), 1.3);
      }
    }
  }

  private checkNoSheepResult(): void {
    if (this.score >= GOAL) return;
    const remaining = this.sheep.filter((sheep) => sheep.alive).length;
    if (remaining === 0) {
      this.finish(false, 'Стадо закончилось', `Соперники унесли овец: ${this.lostSheep}. Для идеальной охоты нельзя позволять им покинуть карту с добычей.`);
    }
  }

  private updatePhase(): void {
    const currentCycle = Math.floor(this.elapsed / CYCLE_TIME);
    if (currentCycle > this.cycleIndex) {
      this.cycleIndex = currentCycle;
      this.dayNumber = currentCycle + 1;
      this.guardLevel = Math.min(3, currentCycle);
      this.repairKits = Math.min(2, this.repairKits + 1);
    }
    const t = this.elapsed % CYCLE_TIME;
    if (t < 50) this.phase = 'День';
    else if (t < 60) this.phase = 'Сумерки';
    else if (t < 110) this.phase = 'Ночь';
    else this.phase = 'Рассвет';

    if (this.phase !== this.previousPhase) {
      if (this.phase === 'Ночь') {
        this.rivalEntriesThisNight = 0;
        this.nextRivalSpawn = 66;
        this.playTone(170, .3, .025, 'triangle');
      }
      this.previousPhase = this.phase;
    }

    const nightFactor = t < 50 ? 0 : t < 60 ? smoothstep((t - 50) / 10) : t < 110 ? 1 : 1 - smoothstep((t - 110) / 10);
    const day = new THREE.Color(0xaacb8b);
    const night = new THREE.Color(0x121b2b);
    const color = day.clone().lerp(night, nightFactor);
    this.scene.background = color;
    if (this.scene.fog instanceof THREE.Fog) this.scene.fog.color.copy(color);
    this.sun.intensity = THREE.MathUtils.lerp(2.1, .35, nightFactor);
    this.sky.intensity = THREE.MathUtils.lerp(1.6, .45, nightFactor);
  }

  private updateCamera(dt: number): void {
    this.cameraTarget.lerp(this.wolf.position, 1 - Math.exp(-3 * dt));
    this.camera.position.x = this.cameraTarget.x + 18;
    this.camera.position.z = this.cameraTarget.z + 18;
    this.camera.lookAt(this.cameraTarget);
  }

  private updateUi(): void {
    const seconds = Math.floor(this.elapsed % CYCLE_TIME);
    ui.phase.textContent = this.phase;
    ui.day.textContent = `День ${this.dayNumber} · охрана ${this.guardLevel + 1}`;
    ui.time.textContent = `${String(Math.floor(seconds / 60)).padStart(2, '0')}:${String(seconds % 60).padStart(2, '0')}`;
    ui.sheep.textContent = `Добыча: ${this.score} / ${GOAL}`;
    ui.lost.textContent = `Потери: ${this.lostSheep}`;
    ui.health.textContent = `Здоровье: ${this.health} / ${this.maxHealth}`;
    ui.form.textContent = `Маскировка: ${this.disguised ? 'надета' : 'снята'}`;
    const costumeLabels = ['порвана', 'повреждена', 'цела'];
    ui.costume.textContent = `Шкура: ${costumeLabels[this.costumeIntegrity]} · ремкомплекты ${this.repairKits}`;
    ui.carrying.textContent = `Добыча в зубах: ${this.playerCarrying ? 'да' : 'нет'}`;
    const progress = this.eatProgress > 0
      ? this.eatProgress / 1.6
      : this.repairProgress > 0
        ? this.repairProgress / 2
        : this.changeProgress / CHANGE_TIME;
    ui.progress.style.width = `${Math.min(100, progress * 100)}%`;

    const dogLabels: Record<DogState, string> = {
      patrol: 'патрулирует',
      alert: 'проверяет подозрение',
      chase: this.dogBiteWindup > 0 ? 'готовит укус!' : 'преследует',
      'search-visual': 'идёт к последней точке',
      'search-scent': 'ищет по запаху',
      return: 'возвращается к стаду',
    };
    ui.danger.textContent = `Пёс: ${dogLabels[this.dogState]} · ${Math.round(this.dogSuspicion)}%`;
    const rivalLabels: Record<RivalState, string> = {
      hidden: 'пока не замечен',
      approach: 'крадётся к стаду',
      carry: 'уносит овцу',
      fight: `дерётся · ${this.rival.hp} HP`,
      retreat: 'отступает',
      'escape-warning': `почти у выхода · ${Math.max(0, 1.2 - this.rival.exitTimer).toFixed(1)} с`,
    };
    ui.rival.textContent = `Соперник: ${rivalLabels[this.rival.state]}`;
    ui.dash.textContent = `Рывок: ${this.dashCooldown <= 0 ? 'готов' : `${this.dashCooldown.toFixed(1)} с`} · приманка: ${this.bleatCooldown <= 0 ? 'готова' : `${this.bleatCooldown.toFixed(1)} с`}`;
    const nearBarn = this.wolf.position.distanceTo(new THREE.Vector3(11, 0, -8)) < 4.5;
    if (this.playerHeld > 0) ui.hint.textContent = `Пёс удерживает: ${this.playerHeld.toFixed(1)} с — Shift для рывка!`;
    else if (this.eatProgress > 0) ui.hint.textContent = `Поедание: ${Math.max(0, 1.6 - this.eatProgress).toFixed(1)} с`;
    else if (this.repairProgress > 0) ui.hint.textContent = `Ремонт маскировки: ${Math.max(0, 2 - this.repairProgress).toFixed(1)} с`;
    else if (this.changeProgress > 0) ui.hint.textContent = `Переодевание: ${Math.ceil(CHANGE_TIME - this.changeProgress)} с`;
    else if (this.isGrazing) ui.hint.textContent = 'Притворно пасётесь: подозрение снижается';
    else if (this.shepherdState === 'aim') {
      const aimDuration = this.playerHeld > 0 ? .45 : .9;
      ui.hint.textContent = `Пастух целится: ${Math.max(0, aimDuration - this.shepherdAim).toFixed(1)} с — уйдите за укрытие!`;
    }
    else if (this.rival.state === 'escape-warning') ui.hint.textContent = 'Соперник почти ушёл! Снимите костюм и ударьте Пробелом';
    else if (this.playerCarrying) ui.hint.textContent = 'Удерживайте E, чтобы съесть овцу; Пробел — бросить';
    else if (nearBarn && this.disguised && this.costumeIntegrity < 2 && this.repairKits > 0) ui.hint.textContent = 'Удерживайте E у сарая, чтобы починить шкуру';
    else if (!this.disguised) ui.hint.textContent = 'Пробел рядом с овцой — схватить; рядом с соперником — ударить';
    else if (this.phase === 'Ночь') ui.hint.textContent = 'Ночью пёс ищет активнее. Не отходите от стада';
    else ui.hint.textContent = 'Удерживайте F неподвижно, чтобы снять маскировку';
  }

  private finish(won: boolean, title: string, text: string): void {
    this.running = false;
    this.finished = true;
    this.paused = false;
    ui.overlayTitle.textContent = title;
    ui.overlayText.textContent = text;
    ui.start.textContent = won ? 'Сыграть ещё раз' : 'Попробовать снова';
    ui.overlay.classList.remove('hidden');
    this.playTone(won ? 659 : 130, .35, .065, won ? 'sine' : 'sawtooth');
  }

  private ensureAudio(): void {
    if (!this.audioContext) this.audioContext = new AudioContext();
    if (this.audioContext.state === 'suspended') void this.audioContext.resume();
  }

  private playTone(frequency: number, duration: number, volume: number, type: OscillatorType = 'sine'): void {
    if (!this.soundEnabled || !this.audioContext) return;
    const oscillator = this.audioContext.createOscillator();
    const gain = this.audioContext.createGain();
    oscillator.type = type;
    oscillator.frequency.value = frequency;
    gain.gain.setValueAtTime(volume, this.audioContext.currentTime);
    gain.gain.exponentialRampToValueAtTime(.0001, this.audioContext.currentTime + duration);
    oscillator.connect(gain).connect(this.audioContext.destination);
    oscillator.start();
    oscillator.stop(this.audioContext.currentTime + duration);
  }

  private showIntro(): void {
    this.running = false;
    this.paused = false;
    ui.overlayTitle.textContent = 'Волк в овечьей шкуре';
    ui.overlayText.textContent = 'Днём смешивайтесь со стадом и выбирайте момент для охоты. Ночью сторожевой пёс становится активнее — теперь охотятся уже на вас.';
    ui.start.textContent = 'Начать забег';
    ui.overlay.classList.remove('hidden');
  }

  private togglePause(): void {
    if (this.finished) return;
    if (this.paused) {
      this.resume();
      return;
    }
    if (!this.running) return;
    this.running = false;
    this.paused = true;
    this.keys.clear();
    ui.overlayTitle.textContent = 'Пауза';
    ui.overlayText.textContent = 'Забег остановлен. Прогресс сохранён.';
    ui.start.textContent = 'Продолжить';
    ui.overlay.classList.remove('hidden');
  }

  private resume(): void {
    this.paused = false;
    this.running = true;
    this.keys.clear();
    ui.overlay.classList.add('hidden');
    this.clock.getDelta();
  }

  private resetSheep(): void {
    for (const sheep of this.sheep) {
      sheep.alive = true;
      sheep.mesh.visible = true;
      sheep.mesh.position.set(random(-12, 9), 0, random(-8, 8));
      sheep.velocity.set(0, 0, 0);
      sheep.turnIn = random(0, 2);
      sheep.state = 'graze';
      sheep.carriedBy = null;
    }
  }

  private resize(): void {
    const aspect = window.innerWidth / window.innerHeight;
    const view = 18;
    this.camera.left = -view * aspect;
    this.camera.right = view * aspect;
    this.camera.top = view;
    this.camera.bottom = -view;
    this.camera.updateProjectionMatrix();
    this.renderer.setSize(window.innerWidth, window.innerHeight);
  }
}

function random(min: number, max: number): number {
  return min + Math.random() * (max - min);
}

function smoothstep(value: number): number {
  const t = THREE.MathUtils.clamp(value, 0, 1);
  return t * t * (3 - 2 * t);
}

function distancePointToSegment(point: THREE.Vector3, start: THREE.Vector3, end: THREE.Vector3): number {
  const segment = end.clone().sub(start).setY(0);
  const toPoint = point.clone().sub(start).setY(0);
  const lengthSq = segment.lengthSq();
  if (lengthSq <= .0001) return toPoint.length();
  const t = THREE.MathUtils.clamp(toPoint.dot(segment) / lengthSq, 0, 1);
  return start.clone().addScaledVector(segment, t).distanceTo(point);
}

new PrototypeGame(required('game'));
