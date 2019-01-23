#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <time.h>
#define impossible -1234
#define must 9999

void draw(int arr[][7]);
int dropstone(int i,int arr[][7],int turn);
int counterpart();

void copyboard(int arr[][7],int brr[][7]);
int check(int arr[][7]);

int ai(int arr[][7],int turn);

int heuristic_function(int arr[][7], int turn,int depth);
int minmax(int heuristic_value[],int d, int arr[][7], int turn);

int win(int arr[][7], int x,int turn);
int lose(int arr[][7], int x,int turn);
int winline_weight(int arr[][7],int x,int turn);
int impede_weight(int arr[][7],int x,int turn);
int winspot_weight(int arr[][7],int x,int turn);

int rule(int start, int arr[][7],int turn);
int make_threat(int arr[][7],int x,int turn);
int check_threat(int arr[][7], int turn);
int useful(int arr[][7], int tr, int tc);
int check_bottom_1(int arr[][7], int x, int turn);
int check_bottom_2(int arr[][7], int x, int turn);
int check_row(int arr[][7], int x);

int state=0,heuristic_value[7000000],dr[7];
int poss=0;
int vv=0;
int fixdepth=7;
int alpha=-99999;
int check_next[7];
int priority_column=-1;

int main(){
    int arr[6][7]={
      {-1,-1,-1,-1,-1,-1,-1},
        {-1,-1,-1,-1,-1,-1,-1},
        {-1,-1,-1,-1,-1,-1,-1},
        {-1,-1,-1,-1,-1,-1,-1},
        {-1,-1,-1,-1,-1,-1,-1},
        {-1,-1,-1,-1,-1,-1,-1}};
    int brr[6][7];
    char start,a;
    int mode;
    int turn=0;
    printf("상대팀이 먼저 플레이 합니까?(Y/N) : ");
    scanf("%c",&start); a=getchar();

    while(1){
       printf("search algorithm 모드는 1, rule 모드는 2를 입력하세요: ");
        scanf("%d",&mode); a=getchar();
        if(mode==1){
              if((start=='y'||start=='Y')&&turn==0){
              draw(arr);
              dropstone(counterpart(),arr,turn); turn++;
              printf("   상대팀   \n");
              draw(arr);
             }

              if((start=='n'||start=='N')&&turn==0){
                dropstone(3, arr, turn);  turn++;
              }
              else{
                  dropstone(ai(arr,turn),arr,turn); turn++;
              }
              printf("    우리팀  \n");
              draw(arr);
              if(check(arr)==1){
                  printf("the end");
                  break;
              }
              dropstone(counterpart(),arr,turn); turn++;
              printf("   상대팀   \n");
              draw(arr);
              if(check(arr)==1){
                  printf("the end");
                  break;
              }
       }
       else if(mode==2){

            if((start=='y'||start=='Y')&&turn==0){
              draw(arr);
              dropstone(counterpart(),arr,turn); turn++;
              printf("   상대팀   \n");
              draw(arr);
             }

            if((start=='n'||start=='N')&&turn==0){
                dropstone(3, arr, turn);  turn++;
              }
            else {
          copyboard(arr,brr);
            dropstone(rule(start,brr,turn),arr,turn); turn++;
        }
          printf("    우리팀  \n");
          draw(arr);
          if(check(arr)==1){
              printf("the end");
             break;
          }
          dropstone(counterpart(),arr,turn); turn++;
          printf("   상대팀   \n");
          draw(arr);
          if(check(arr)==1){
              printf("the end");
              break;
          }
       }
       else {
          printf("모드를 잘못입력하셨습니다. 다시 입력해주세요.");
       }

    }
    return 0;
}

void draw(int arr[][7]){
    int i,k=0;
    for(i=5;i>=0;i--){
      printf("%d ", (i+1));
        for(k=0;k<=6;k++){
            if(arr[i][k]==-1){
                printf("· ");
            }
            else if(arr[i][k]==0){
                printf("● ");
            }
            else{
                printf("○ ");
            }
        }
        printf("\n");
    }
    printf("   1  2  3  4  5  6  7\n\n");
}

int counterpart(){
    int put;
    char a;
    printf("상대팀이 돌 놓은 위치 : ");
    scanf("%d",&put); a=getchar();
    put=put-1;
    return put;
}

int dropstone(int i,int arr[][7],int turn){
    int k;
    if(i==-100){printf("기권\n");}
    if(arr[5][i]!=-1){
        return 1;
    }
    for(k=0;k<6;k++){
        if(arr[k][i]==-1){
            arr[k][i]=turn%2;
            break;
        }
    }
    return 0;
}

void copyboard(int arr[][7],int brr[][7]){
    int i,j;
    for(i=0;i<6;i++){
        for(j=0;j<7;j++){
            brr[i][j]=arr[i][j];
        }
    }
}
//--------------------------------여기까지 인터페이스 관련 이 밑으로는 ai----------------------------------------------------//

int ai(int arr[][7],int turn){
    int i,aii,a,b,enemy,mine,br[8],max=-9999;
    enemy=(turn+1)%2;
    mine=turn%2;

    poss=0; //채워져 있는 칸이 몇개인지 계싼
    for(a=0;a<6;a++){
        for(b=0;b<7;b++){
            if(arr[a][b]!=-1){
                poss++;
            }
        }
    }
    switch(poss) {
        case 41 :
            fixdepth = 1;
            break;
        case 40 : case 39 : case 38 :
            fixdepth = 3;
            break;
        case 37 : case 36 : case 35 : case 34 :
            fixdepth = 5;
            break;
        default :
            fixdepth = 7;
            break;
    }

    state=0;

    aii=heuristic_function(arr,turn,fixdepth);

    if(fixdepth==7 && aii==-3) //모든 column이 도일한 값을 가질 때
    {
         for(a=0;a<7;a++){
            br[a]=winline_weight(arr, a, turn)+winspot_weight(arr, a, turn)+impede_weight(arr,a,turn)+win(arr, a, turn);
            printf("%d ",br[a]); //각 column에 대해 휴리스틱값 계산해서
            if(max<=br[a]){
                aii=a; // 최대 값을 가지는 column을 aii값으로
            }
        }
        printf("heuristic function 값\n");
        return aii;
    }
    return aii;
}

int priority(int arr[][7], int turn)
{
    int i,aii,a,b,enemy,mine;
    enemy=(turn+1)%2;
    mine=turn%2;
    // ● : 상태방 돌 / ○ : 내 돌 / _ : 빈칸
    if(turn==1){ //지금 차례가 두번째로 두는 돌이면

            if(arr[0][1]!=-1){
                    return 2;
            }
            if(arr[0][5]!=-1){
                    return 4;
            }
            /*첫번째 돌이 두번째 칸이라면 그 오른쪽에, 여섯번째 칸이라면 그 왼쪽에 놓는다
             <_ ● ○ _ _ _ _> 또는 <_ _ _ _ ○ ● _>*/
    }
    for(i=0;i<7;i++){ //왼쪽부터 오른쪽으로 항을 훑으면서 내가 두면 이기는 column이 있나 체크
        if(win(arr, i, turn)==1000){
            return i; //있으면 해당 column을 리턴
        }
    }
    for(i=0;i<7;i++){ //마찬가지로 상대방이 두면 이기는 column이 있나 체크
        if(lose(arr, i, turn)==500){
           return i;
        }
    }
     if(poss==41){
        for(a=0;a<6;a++){if(arr[5][a]==-1){
                return a;}}
    }
    for(a=0;a<6;a++){ //맨 아래 row부터 위로 올라가며 체크
        for(i=0;i<=2;i++){ //맨 왼쪽부터 세번째 column까지 체크
            if(a==0){ //맨 아래 row에 대해서
                //비어있는 제일 왼쪽 항에 대해
                if((arr[a][i]==-1)&&(arr[a][i+1]==enemy)&&(arr[a][i+2]==enemy)&&(arr[a][i+3]==-1)&&(arr[a][i+4]==-1)){
                   if(i==0||i==1){return i+3;} else{return i;}
                /*오른쪽 두개가 상대방 돌이고 그 오른쪽 두개가 비어있으면 < _ ● ● _ _ >
                  해당 column이
                  첫번째 두번째 --> 상대방 돌 바로 오른편에 둔다 < _ ● ● ○ _ >
                  세번째 이상 --> 그 자리에 둔다 < ○ ● ● _ _ >
                */
                }
                if((arr[a][i]==-1)&&(arr[a][i+1]==-1)&&(arr[a][i+2]==enemy)&&(arr[a][i+3]==enemy)&&(arr[a][i+4]==-1)){
                    if(i==0){return i+4;} else{return i+1;}
                }
                /*바로 오른편은 비어있고 그 너머 두칸이 상대방, 그 오른편은 빈칸이라면 < _ _ ● ● _ >
                  해당 column이
                  첫번째 --> 상대방 돌 바로 오른편에 둔다 < _ _ ● ● ○ >
                  그 이상 --> 상대방 돌 바로 왼편에 둔다 < _ ○ ● ● _ >
                */
                if((arr[a][i]==-1)&&(arr[a][i+1]==enemy)&&(arr[a][i+2]==-1)&&(arr[a][i+3]==enemy)&&(arr[a][i+4]==-1)){

                    return i+2;
                }
                /*바로 오른편이 상대방 그리고 한칸 너머로 또 상대방 돌 < _ ● _ ● _ >
                  상대방 돌 사이에 둔다 < _ ● ○ ● _ >
                */
            }
            else{
                if((arr[a-1][i]!=-1)&&(arr[a-1][i+1]!=-1)&&(arr[a-1][i+2]!=-1)&&(arr[a-1][i+3]!=-1)&&(arr[a-1][i+4]!=-1)){
                /*두번째 이상의 row에 대해 &&
                바로 아랫줄의 해당 column과 그 오른쪽으로 4칸이 차있을 경우에 대해
                [ _ ? ? ? ? ]
                [ @ @ @ @ @ ] (@ : 상대방, 자신의 돌 상관없이 채워져 있는 상태)
                나머지 룰은 위와 동일하게 적용됨
                */
                    if((arr[a][i]==-1)&&(arr[a][i+1]==enemy)&&(arr[a][i+2]==enemy)&&(arr[a][i+3]==-1)&&(arr[a][i+4]==-1)){
                            if(i==0||i==1){return i+3;} else{return i;}
                    }
                    if((arr[a][i]==-1)&&(arr[a][i+1]==-1)&&(arr[a][i+2]==enemy)&&(arr[a][i+3]==enemy)&&(arr[a][i+4]==-1)){
                        if(i==0){return i+4;} else{return i+1;}
                    }
                    if((arr[a][i]==-1)&&(arr[a][i+1]==enemy)&&(arr[a][i+2]==-1)&&(arr[a][i+3]==enemy)&&(arr[a][i+4]==-1)){
                        return i+2;
                    }
                }
            }
        }
    }
}

typedef struct _list{
        struct _node *cur;
        struct _node *head;
        struct _node *tail;
}linkedList;

typedef struct _node {
    int data[6][7];
    struct _node *next;
} node;

void initList(linkedList * L)
{

    L->cur = NULL;
    L->head = NULL;
    L->tail = NULL;

}

void createNode(linkedList *L, int tdata[6][7])
{
    node * newNode = (node *)malloc(sizeof(node));
    copyboard(tdata,newNode->data);
    newNode->next = NULL;
    if(L->head==NULL&&L->tail==NULL)
    {
        L->head=L->tail=newNode;
    }
    else{
        L->tail->next = newNode;
        L->tail = newNode;
    }
}

void deleteLastNode(linkedList *L)
{
    node *p = L->head;
    while(p->next->next!=NULL)
        p=p->next;
    p->next = p->next->next;
    L->tail = p;
}

int for_hu(linkedList * L, int turn, int depth)
{
    int i, j, max=0, min=9999, a, b, num=0;
    int copy[6][7];
    int initcopy[6][7];

    if(depth==1){

         for(j=0;j<(int)pow(7,fixdepth);j++){

            copyboard(L->head->data, initcopy);
            copyboard(initcopy, copy);
            num=0;
            max=0, min=9999;


            for(a=0;a<6;a++){
                    for(b=0;b<7;b++){

                        if(copy[a][b]!=-1){
                            num++;
                        }
                    }
                }

            if(num-poss==fixdepth-1){
            //상대가 내가 놓은 위치에 놓거나, poss<=25이고 4목을 완성했을 경우, heuristic_value[]=-1234(impossible)
                    if(check(copy)==1&&poss<=25){
                            heuristic_value[state]=impossible;
                        }
                    else{
                       //휴리스틱 값 계산.
                            heuristic_value[state]=winline_weight(copy, j%7, turn)+winspot_weight(copy, j%7, turn)+impede_weight(copy, j%7,turn)+win(copy, j%7, turn);

                        }
            }
            else{
                    heuristic_value[state]=impossible;
            }


                state++;//0->1->2->....->
                if(j%7==6){

                    L->head = L->head->next;
                }
         }

              for(i=0;i<7;i++)
              {


                    for(j=(int)(((int)pow(7,6))*i);j<(int)(((int)pow(7,6))*(i+1));j++){

                        if(check_next[i]==impossible)
                        {
                            heuristic_value[j]=impossible;

                        }
                         if(priority_column==i)
                        {
                                heuristic_value[j]=must;
                        }
                    }
                    check_next[i]=0;
                }
              state=0;
              priority_column=-1;

            return 0;
    }
    else if(depth==fixdepth)
    {
        int jj;
         for(j=0;j<(int)pow(7,(fixdepth-depth+1));j++){

                copyboard(L->head->data, initcopy);
                copyboard(initcopy, copy);
                dropstone(j%7, copy, turn);
                createNode(L, copy);

                priority_column=priority(initcopy, turn);//이건 무조건 놓아야하는 경우.

                if(win(copy, j%7, turn+1)==1000){

                        check_next[j%7]=impossible;
                }

                copyboard(copy,initcopy);


                if(j%7==6){
                    node * p = L->head;
                    L->head = L->head->next;
                    free(p);
                }
                jj=j;
                if(priority_column!=-1)
                {
                    break;
                }//이게 지금 개개개문제.break하면 남은 상황에대해서 안만들어져 그럼 안돼. 이걸 어떻게 처리하냐.아.아 아 ㅇ ㅏㅇ ㅏ아아ㅏ

        }

        for(jj=jj+1;jj<7;jj++)
        {

                copyboard(L->head->data, initcopy);
                copyboard(initcopy, copy);
                dropstone(jj%7, copy, turn);
                createNode(L, copy);

                if(win(copy, jj%7, turn+1)==1000){

                        check_next[jj%7]=impossible;
                }
                copyboard(copy,initcopy);

                if(jj%7==6){
                    node * p = L->head;
                    L->head = L->head->next;
                    free(p);
                }
        }

        for_hu(L, turn+1, depth-1);
    }
    else if(depth<fixdepth){
        for(j=0;j<(int)pow(7,(fixdepth-depth+1));j++){

                copyboard(L->head->data, initcopy);
                copyboard(initcopy, copy);
                dropstone(j%7, copy, turn);
                createNode(L, copy);
                copyboard(copy,initcopy);

                if(j%7==6){
                    node * p = L->head;
                    L->head = L->head->next;
                    free(p);
                }
        }
        for_hu(L, turn+1, depth-1);
        return 0;
    }
    return 0;

}


int heuristic_function(int arr[][7], int turn, int depth)
{

    linkedList *L = (linkedList *)malloc(sizeof(linkedList));
    L->cur = NULL;
    L->head = NULL;
    L->tail = NULL;
    int i, j, max=0, min=9999, a, b, num=0;
    int copy[6][7];
    int copyturn = turn;

    copyboard(arr,copy);

    createNode(L, arr);

    //휴리스틱 값 계산.
    for_hu(L, turn, depth);

    if(depth==fixdepth){
        return minmax(heuristic_value,fixdepth, arr, copyturn);//minmax는 max값을 갖는 col_num 혹은 -3 반환
    }
    return 0;

}

int minmax(int heuristic_value[],int d, int arr[][7],int turn){
    int i=0,j=0,dab[7],p=0,v,o;
    int max=-1000,min=99999;
    int copy[6][7];
    copyboard(arr, copy);


    for(i=d;i>=0;i--){
        for(j=0;j<(int)pow(7,i);j++){
            if(i==1){

                copyboard(arr, copy);
                dropstone(j,copy,turn);

                if(heuristic_value[j]>1300&&heuristic_value[j]!=-99999&&j==3){
                        heuristic_value[j]-=5;
                }
                /*if(win(copy, j, turn+1)==1000)
                    {
                            heuristic_value[j]=-99999;

                    }// 내가둔곳위에 상대방이 두었는데, 내가 지는 상황이면 체크해놨다가 임파시블로
                copyboard(arr,copy);
                */

                printf("%d ",heuristic_value[j]);
                if(j==6){
                    printf("heuristic function 값\n");

                }
                dab[j]=heuristic_value[j];
            }
            if(i%2==1){
                if(max<heuristic_value[j]){
                    max=heuristic_value[j];
                }
            }
            else{
                if(min>heuristic_value[j]){
                    min=heuristic_value[j];
                }
            }
            if(i==1&&j==6){
                srand((unsigned int)time(NULL));

                while(1){
                    p=rand()%7;
                    if(heuristic_value[p]==max){
                        return p;
                    }
                    if(heuristic_value[0]==-99999&&heuristic_value[1]==-99999&&heuristic_value[2]==-99999&&heuristic_value[3]==-99999&&heuristic_value[4]==-99999&&heuristic_value[5]==-99999&&heuristic_value[6]==-99999){
                        return -3;
                    }
                }
            }
            if(j%7==6){
                if(i%2==1){
                    if(max==-1234||max==-1000){
                        heuristic_value[(j+1)/7-1]=99999;
                    }
                    else if(max==9999)
                    {
                        heuristic_value[(j+1)/7-1]=-9999;
                    }
                    else{
                        heuristic_value[(j+1)/7-1]=max;
                    }
                }
                else{
                    if(min==-1234||min==99999){
                        heuristic_value[(j+1)/7-1]=-99999;
                    }
                    else if(min==-9999)
                    {
                        heuristic_value[(j+1)/7-1]=9999;
                    }
                    else{
                        heuristic_value[(j+1)/7-1]=min;
                    }
                }
                max=-1000;min=99999;
            }
        }
    }
    return dab[0];
}



//---------------------여기까지 ai 이 밑으로는 ai아닌 함수들-----------------------------------------//

//네개 연속 같은 값인지
int check(int arr[][7]){
   int i,j;
   //세로 4개 연속인가 확인
   for(i=0;i<=2;i++){
      for(j=0;j<=6;j++){
         if(arr[i][j]!=-1){
            if(arr[i][j]==arr[i+1][j]&&arr[i][j]==arr[i+2][j]&&arr[i][j]==arr[i+3][j]) return 1;
         }
      }
   }
   //가로 4개 연속인가 확인
   for(i=0;i<=5;i++){
      for(j=0;j<=3;j++){
         if(arr[i][j]!=-1){
            if(arr[i][j]==arr[i][j+1]&&arr[i][j]==arr[i][j+2]&&arr[i][j]==arr[i][j+3]) return 1;
         }
      }
   }
    //슬래시 방향 대각선으로  4개 연속인가 확인
    for(i=0;i<=2;i++){
       for(j=0;j<=3;j++){
          if(arr[i][j]!=-1){
             if(arr[i][j]==arr[i+1][j+1]&&arr[i][j]==arr[i+2][j+2]&&arr[i][j]==arr[i+3][j+3]) return 1;
          }
       }
    }
    //역슬래시 방향 대각선으로 4개 연속인가 확인
   for(i=0;i<=2;i++){
      for(j=3;j<=6;j++){
         if(arr[i][j]!=-1){
            if(arr[i][j]==arr[i+1][j-1]&&arr[i][j]==arr[i+2][j-2]&&arr[i][j]==arr[i+3][j-3]) return 1;
         }
      }
   }
   //연속 4개가 어떻게든 안생기면
    return 0;
}

int win(int arr[][7],int x,int turn){
    int i,y=0;
    //말이 몇번째 칸까지 놓여있는지 확인
    for(i=5;i>=0;i--){
        if(arr[i][x]!=-1){
            y=i+1; break;
        }
    }
    if(y==6){return impossible;}

    //y,x에 내가 놓는 상황 가정해봄
    arr[y][x]=turn%2;
    //그때 check=1즉 4개가 연속되서 이기는 상황
    if(check(arr)==1){
       //가정 끝 원래대로하자
        arr[y][x]=-1;
        return 1000;
    }
    //즉 4개가 연속되서 이기지 않는 상황이니까 여기다 놓을 필요 없으니까 원상복귀+리턴값도 그냥 0
    arr[y][x]=-1;
    return 0;
}

//win하고 반대 상대가 두면 지는 거
int lose(int arr[][7],int x,int turn){
    int i,y=0;
    for(i=5;i>=0;i--){
        if(arr[i][x]!=-1){
            y=i+1; break;
        }
        if(i==0){
            y=0;
        }
    }
    if(y==6){return impossible;}
    arr[y][x]=(turn+1)%2;
    if(check(arr)==1){
        arr[y][x]=-1;
        return 500;
    }
    arr[y][x]=-1;
    return 0;
}

int winline_weight(int arr[][7],int x,int turn){
    int i,j,w=0,y=0,mine,enemy;

    //i,x에 말이 있나 없나 확인 없으면 거기다 놓을라고 i,x에 말이있으면 그 위에 두어야 함 그래서 y=i+1
    for(i=5;i>=0;i--){
        if(arr[i][x]!=-1){
            y=i+1;
         break;
        }
    }
    //y=6이면 그 줄이 꽉 찬것 더이상 못놓으니까 임파서블
    if(y==6){return impossible;}

    //y,x에 내가 놓는 상황 만듬
    arr[y][x]=turn%2;

    mine=turn%2;
    enemy=(turn+1)%2;

    /*
    가로 연속 4개가 상대말이 아닌게 있을때마다 w 올려주기
               나의말이 아닌게 있을때마다 w 내려주기
   여기서 w는 가중치
    */
    for(i=0;i<6;i++){
    //여기서 i는 배열의 가로 줄
        for(j=0;j<4;j++){
           //여기서 j는 배열의 세로줄, 4칸이 연속되나 확인하므로 j가 0일때 0-3, j가 1일때 1-4, j가 2일때 2-5, j가 3일때 3-6칸 확인
            if(arr[i][j]!=enemy&&arr[i][j+1]!=enemy&&arr[i][j+2]!=enemy&&arr[i][j+3]!=enemy){
                w++;
            }
            if(arr[i][j]!=mine&&arr[i][j+1]!=mine&&arr[i][j+2]!=mine&&arr[i][j+3]!=mine){
                w--;
            }
        }
    }

   /*
    세로  연속 4개가 상대말이 아닌게 있을때마다 w 올려주기
               나의말이 아닌게 있을때마다 w 내려주기
   여기서 w는 가중치
    */
    for(j=0;j<7;j++){
    //여기서 j는 세로줄
        for(i=0;i<3;i++){
        //여기서 i는 배열의 가로줄, 4줄이 연속되나 확인하므로 i가 0일때 0-3, i가 1일때 1-4, i가 2일때 2-5 줄 확인
            if(arr[i][j]!=enemy&&arr[i+1][j]!=enemy&&arr[i+2][j]!=enemy&&arr[i+3][j]!=enemy){
                w++;
            }
            if(arr[i][j]!=mine&&arr[i+1][j]!=mine&&arr[i+2][j]!=mine&&arr[i+3][j]!=mine){
                w--;
            }
        }
    }

   /*
    대각선  연속 4개가 상대말이 아닌게 있을때마다 w 올려주기
               나의말이 아닌게 있을때마다 w 내려주기
   여기서 w는 가중치
    */

    for(i=0;i<3;i++){
       //오른쪽 아래 방향 대각선
        for(j=0;j<4;j++){
            if(arr[i][j]!=enemy&&arr[i+1][j+1]!=enemy&&arr[i+2][j+2]!=enemy&&arr[i+3][j+3]!=enemy){
                w++;
            }
            if(arr[i][j]!=mine&&arr[i+1][j+1]!=mine&&arr[i+2][j+2]!=mine&&arr[i+3][j+3]!=mine){
                w--;
            }
        }
        //왼쪽 아래 방향 대각선
        for(j=6;j>=3;j--){
            if(arr[i][j]!=enemy&&arr[i+1][j-1]!=enemy&&arr[i+2][j-2]!=enemy&&arr[i+3][j-3]!=enemy){
                w++;
            }
            if(arr[i][j]!=mine&&arr[i+1][j-1]!=mine&&arr[i+2][j-2]!=mine&&arr[i+3][j-3]!=mine){
                 w--;
            }
        }
    }

    //원래대로 해줌
    arr[y][x]=-1;

    //turn이 작을때는 빈칸이 많아서 w가 올라가기 쉽기 때문에 조절해줌
    if(turn>13){return w/2;}
    return w*3;
}


int impede_weight(int arr[][7], int x,int turn){
    int brr[6][7],imp=0,i,y=0,enemy,mine,j;

   //이부분은 항상 확인하는거 이 판이 끝까지 찼는지 안찼는지
   for(i=5;i>=0;i--){
        if(arr[i][x]!=-1){
            y=i+1; break;
        }
    }
    if(y==6){return impossible;}

    //y,x에 내가 놓는 상황 만듬
    arr[y][x]=(turn)%2;
    //상대는 다음턴 나는 이번턴
    mine=turn%2;
    enemy=(turn+1)%2;

   /*내가 y,x에 두면 세로로 연속 두개인 상대말을 막는지 확인 막으면 imp 올리자
   나
   상대
   상대
   */
         if(y>=2&&arr[y-1][x]==enemy&&arr[y-2][x]==enemy) imp++;

   /*내가 y,x에 두면 가로로  연속 두개인 상대말을 막는지 확인 막으면 imp 올리자
   나 상대 상대
   상대 상대 나
   */
         if(x<=4&&arr[y][x+1]==enemy&&arr[y][x+2]==enemy) imp++;
         if(x>=2&&arr[y][x-1]==enemy&&arr[y][x-2]==enemy) imp++;

      /*내가 y,x에 두면 대각선으로  연속 두개인 상대말을 막는지 확인 막으면 imp 올리자
   나                         나       상대               상대
      상대                상대          상대          상대
         상대          상대                나      나
   */
      if(y>=2&&x<=4&&arr[y-1][x+1]==enemy&&arr[y-2][x+2]==enemy) imp++;
      if(y>=2&&x>=2&&arr[y-1][x-1]==enemy&&arr[y-2][x-2]==enemy) imp++;
      if(y<=4&&x>=2&&arr[y+1][x-1]==enemy&&arr[y+2][x-2]==enemy) imp++;
      if(y<=4&&x<=4&&arr[y+1][x+1]==enemy&&arr[y+2][x+2]==enemy) imp++;

     //위에서 바꿔놔서 초기화 함
    arr[y][x]=-1;

    return imp*7;
}


int winspot_weight(int arr[][7],int x,int turn){
    int i,y=0,j,mywin=0,yourwin=0,spot=0;

   //다음말을 어디에 둘지
   for(i=5;i>=0;i--){
        if(arr[i][x]!=-1){
            y=i+1; break;
        }
        if(i==0){
            y=0;
        }
    }
    if(y==6){return impossible;}

    //y,x에 내가 놓는 상황 만듬
    arr[y][x]=(turn)%2;

   for(j=0;j<7;j++){
        for(i=0;i<6;i++){
            //i,j밑에는 말이 놓여있고 이제 여기 놓을 차례
            if(arr[i][j]==-1){

            //내턴에서 이길수있나
               arr[i][j]=turn%2;
                    if(check(arr)==1){
                     //내가 이길수 있으니까
                        mywin++;

                  //i,j에 상대가 놓고 그 위에 내가 놓아도 이기면 spot올려줌
                  if(i<5){
                     arr[i][j]=(turn+1)%2;
                     arr[i+1][j]=turn%2;
                        if(check(arr)==1) spot+=351;
                     arr[i+1][j]=-1;
                     arr[i][j]=-1;
                  }

                    }

               //상대턴에서 이길수있나
                    arr[i][j]=(turn+1)%2;
                    if(check(arr)==1){
                        //상대가 이기니까
                        yourwin++;
                  //i,j에 내가놓고 그 위에 상대가 놓아도 상대가 이기면 망하니까 spot 내려줌
                  if(i<5){
                     arr[i][j]=turn%2;
                     arr[i+1][j]=(turn+1)%2;;
                        if(check(arr)==1) spot-=403;
                     arr[i+1][j]=-1;
                     arr[i][j]=-1;
                  }
                    }

                break;
            }
        }
    }

    if(mywin>=2&&yourwin==0){
    //내가 이길 가능성 높은거
        spot+=351;
    }
    if(yourwin>=2&&mywin==0){
    //상대방이 이길 가능성 높은거
        spot-=403;
    }

    //아까 위에서 y,x에 내가 놓는다고 가정했었어서 원상복구
    arr[y][x]=-1;

    //spot이 0보다 크면 내가 유리하고 spot이 0보다 작으면 상대가 유리한 상황
     return spot;
}


//------------------------------------함수 for rule----------------------------------------//
//------------------------------------함수 for rule----------------------------------------//
int rule(int start,int arr[][7],int turn){
   int i,mine,enemy,a,threat_value,temp_col;
   int temp_arr[7]={0}; //각 점수값을 지니는 임시 col array
   int copy[6][7];
   int state=0; //case 8로 넘어가기 전 col value를 판단하기 위한 변수

   threat_value=0;
   temp_col=-1;
   mine=turn%2;
   enemy=(turn+1)%2;

   copyboard(arr,copy);

    //turn이 매우 작을때 최적의 수 계산한 것
    if(turn<=3){
      printf("Rule 모드 판단 turn<=3일 경우\n");
      //상대팀 먼저
      if(start=='y'||start=='Y'){
         if(turn==1){
            if(arr[0][0]==enemy) return 3;
            if(arr[0][1]==enemy) return 2;
            if(arr[0][2]==enemy) return 3;
            if(arr[0][3]==enemy) return 3;
            if(arr[0][4]==enemy) return 3;
            if(arr[0][5]==enemy) return 4;
            if(arr[0][6]==enemy) return 3;
         }
         else if(turn==3){
            if(arr[0][0]==enemy&&arr[0][3]==mine){
               if(arr[1][0]==enemy) return 3;
               if(arr[0][1]==enemy) return 3;
               if(arr[0][2]==enemy) return 3;
               if(arr[1][3]==enemy) return 3;
               if(arr[0][4]==enemy) return 3;
               if(arr[0][5]==enemy) return 4;
               if(arr[0][6]==enemy) return 5;
            }
            if(arr[0][1]==enemy&&arr[0][2]==mine){
               if(arr[0][0]==enemy) return 2;
               if(arr[1][1]==enemy) return 2;
               if(arr[1][2]==enemy) return 2;
               if(arr[0][3]==enemy) return 3;
               if(arr[0][4]==enemy) return 2;
               if(arr[0][5]==enemy) return 6;
               if(arr[0][6]==enemy) return 5;
            }
            if(arr[0][2]==enemy&&arr[1][2]==mine) {
               if(arr[0][0]==enemy) return 3;
               if(arr[0][1]==enemy) return 4;
               if(arr[2][2]==enemy) return 3;
               if(arr[0][3]==enemy) return 1;
               if(arr[0][4]==enemy) return 3;
               if(arr[0][5]==enemy) return 2;
               if(arr[0][6]==enemy) return 2;
            }
            if(arr[0][2]==enemy&&arr[0][4]==mine) {
               if(arr[0][0]==enemy) return 1;
               if(arr[0][1]==enemy) return 1;
               if(arr[1][2]==enemy) return 2;
               if(arr[0][3]==enemy) return 3;
               if(arr[1][4]==enemy) return 4;
               if(arr[0][5]==enemy) return 4;
               if(arr[0][6]==enemy) return 4;
            }
            if(arr[0][3]==enemy&&arr[1][3]==mine) {
               if(arr[0][0]==enemy) return 3;
               if(arr[0][1]==enemy) return 2;
               if(arr[0][2]==enemy) return 1;
               if(arr[2][3]==enemy) return 3;
               if(arr[0][4]==enemy) return 2;
               if(arr[0][5]==enemy) return 3;
               if(arr[0][6]==enemy) return 4;
            }
            if(arr[0][4]==enemy&&arr[0][2]==mine) {
               if(arr[0][0]==enemy) return 2;
               if(arr[0][1]==enemy) return 2;
               if(arr[1][2]==enemy) return 2;
               if(arr[0][3]==enemy) return 3;
               if(arr[1][4]==enemy) return 4;
               if(arr[0][5]==enemy) return 5;
               if(arr[0][6]==enemy) return 5;
            }
            if(arr[0][4]==enemy&&arr[1][4]==mine) {
               if(arr[0][0]==enemy) return 4;
               if(arr[0][1]==enemy) return 4;
               if(arr[0][2]==enemy) return 3;
               if(arr[0][3]==enemy) return 5;
               if(arr[2][4]==enemy) return 3;
               if(arr[0][5]==enemy) return 3;
               if(arr[0][6]==enemy) return 3;
            }
            if(arr[0][5]==enemy&&arr[0][4]==mine) {
               if(arr[0][0]==enemy) return 4;
               if(arr[0][1]==enemy) return 4;
               if(arr[0][2]==enemy) return 4;
               if(arr[0][3]==enemy) return 3;
               if(arr[1][4]==enemy) return 4;
               if(arr[1][5]==enemy) return 5;
               if(arr[0][6]==enemy) return 4;
            }
            if(arr[0][6]==enemy&&arr[0][3]==mine) {
               if(arr[0][0]==enemy) return 2;
               if(arr[0][1]==enemy) return 3;
               if(arr[0][2]==enemy) return 3;
               if(arr[1][3]==enemy) return 3;
               if(arr[0][4]==enemy) return 3;
               if(arr[0][5]==enemy) return 3;
               if(arr[1][6]==enemy) return 3;
            }
         }

      }
      //우리팀 먼저
      else if(start=='n'||start=='N'){
         if(turn==0) return 3;
         else if(turn==2) {
            if(arr[0][0]==enemy) return 3;
            if(arr[0][1]==enemy) return 5;
            if(arr[0][2]==enemy) return 5;
            if(arr[1][3]==enemy) return 3;
            if(arr[0][4]==enemy) return 1;
            if(arr[0][5]==enemy) return 1;
            if(arr[0][6]==enemy) return 3;
         }
      }
      //위에 경우에 안걸리면 가운데 놓는게 제일 확률 높음
      return 3;
   }

   //turn이 3보다 큰 보통의 경우
   else{

    /*반드시 두어야 하는 곳
    1. 내 connect를 완성시킬 수 있는 곳 -> win
    2. 상대방이 두면 connect 완성시킬 수 있는 곳 ->lose

    /**useful threat : 밑받침이 있는 threat
       useless threat : 밑받침이 없어 바로 control 하지 못하는 threat*/

    //useful threat만들기
    /*1. useful threat 2개 만드는 수
      2. useful threat 1개, useless threat 1개 만드는 수
      3. useful threat 1개 만드는 수 */

    //밑받침 수 계산하기
    /*1. 상대방으로 하여금 connect를 완성할 수 있게 해주는 밑받침 선택하면 안됨 --> 둔다고 가정했을 때 상대방돌을 그 위에 올려봄
      2. 상대방으로 하여금 두개의 threat을 생성할 수 있게 해주는 밑받침은 선택하면 안됨 -->둔다고 가정했을때 상대방인척하고 make_threat돌 림
      3. 상대방이 내 threat을 제거할 수 있게 해주는 밑받침은 선택하면 안됨 -->둔다고 가정했을때하고 그 위에도 둔다고 가정 연결되면 2줌 */

    //여기에서 걸러진 나머지 수에 대해서
    /*1. useless threat 2개 만드는 수
      2. useless threat 1개 만드는 수
      3. odd번째 row에*/

    //나머지 경우에 대해선 랜덤으로

    /**최우선순위 win, lose*/

    for(i=0;i<7;i++){ //왼쪽부터 오른쪽으로 항을 훑으면서 내가 두면 이기는 column이 있나 체크
       if(win(arr, i, turn)==1000){
          printf("Rule 모드 판단 case 0\n");
          return i;
        }
    }
    for(i=0;i<7;i++){ //마찬가지로 상대방이 두면 이기는 column이 있나 체크
        if(lose(arr, i, turn)==500){
          printf("Rule 모드 판단 case 0\n");
          return i;
        }
    }

    /**이후에 최우선으로 고려되어야 할 사항
    //밑받침 수 계산하기
    /*1. 상대방으로 하여금 connect를 완성할 수 있게 해주는 밑받침 선택하면 안됨 --> 둔다고 가정했을 때 상대방돌을 그 위에 올려봄*/
    /*돌을 둘 수 있는 column인지
    두 경우에 대해선 temp_arr에 -100값을 줌*/

    for(i=0;i<7;i++){
      if(check_row(copy,i)==-1){temp_arr[i]=-100;}
      else if(check_bottom_1(copy,i,turn)==1){temp_arr[i]=-100;}
    }

    //상대방이 useful threat 2개 만들어 버리면 확실하게 짐
    //만들지 못하도록 그 자리를 선점해야함

    for(i=0;i<7;i++){
      if(temp_arr[i]>-90){
        if(make_threat(copy, i, turn+1)>=8){printf("Rule 모드 판단 case 1\n");return i;}//상대방인 척 하고 돌을 둬보는것임 -->useful threat2개 생기면 그자리 선점
      }
    }

    //useful threat만들기
    /*1. useful threat 2개 만드는 수
      2. useful threat 1개, useless threat 1개 만드는 수
      3. useful threat 1개 만드는 수 */

    //위의 두 경우를 먼저 걸러내고 나머지 column에 대해 계산함
    for(i=0;i<7;i++){ //왼쪽부터 오른쪽으로 항을 훑으면서 threat점수를 살핌 --> 경우의 수 8 4 2 1 최댓값인 value와 그것을 만드는 column 찾음
        if(temp_arr[i]>-90){ //위의 두 경우가 아닌 column에 대해
            if(make_threat(copy, i, turn)>0){ //각 column에 대해 threat value를 계산함
                if(make_threat(copy, i, turn)>threat_value){
                    threat_value=make_threat(copy, i, turn); //최대 threat value를 찾고
                    temp_col=i; //해당 column값을 temp_col에 담아놓음
                }
            }
        }
    }

    if(threat_value>=8){printf("Rule 모드 판단 case 2\n");return temp_col;} //useful threat 2개일 경우
    if(threat_value>=5){printf("Rule 모드 판단 case 3\n");return temp_col;} //useful threat 1개, useless threat 1개일 경우
    if(threat_value>=4){printf("Rule 모드 판단 case 4\n");return temp_col;} //useful threat 1개일 경우

    //밑받침 수 계산하기
    /*1. 상대방으로 하여금 connect를 완성할 수 있게 해주는 밑받침 선택하면 안됨 --> 위에서 걸러낸 조건
      2. 상대방으로 하여금 두개의 threat을 생성할 수 있게 해주는 밑받침은 선택하면 안됨 -->둔다고 가정했을때 상대방인척하고 make_threat돌림*/

    //밑받침 수 계산하기
    for(i=0;i<7;i++){
        if(temp_arr[i]>-90){ //돌을 둘 수 있는 column에 대해
            temp_arr[i]=check_bottom_2(copy,i,turn); //column마다 점수
        }
    }

    //여기에서 걸러진 나머지 수에 대해서
    /*1. useless threat 2개 만드는 수
      2. useless threat 1개 만드는 수
      3. odd번째 row에*/

    if(threat_value>=2){
      if((temp_arr[temp_col]>-90)&&(temp_arr[temp_col]<4)){printf("Rule 모드 판단 case 5\n");return temp_col;} //useless threat 2개
    }

    if(threat_value>=1){
      if((temp_arr[temp_col]>-90)&&(temp_arr[temp_col]<4)){printf("Rule 모드 판단 case 6\n");return temp_col;} //useless threat 1개
    }

    for(i=0;i<7;i++){
      if(temp_arr[i]>-90&&temp_arr[i]<4){
        if(check_row(copy,i)%2==0){printf("Rule 모드 판단 case 7\n");return i;} //odd 번째 row인 것을 선택
      }
    }

    //위의 해당사항이 모두 없다면 돌을 둘 수 있는 column에 대해 랜덤으로 리턴

    //temp_arr이 -100을 가지는 경우 1.돌을 놓을 수 없을 경우 2.그 자리에 돌을 놓는다면 바로 지는 경우
    /*위에서 걸러지지 않는 column에 대해
    위의 두 경우에 해당되지 않는 column을 우선적으로 선택해야함-->state == 1
    위의 두 경우에 해당되는 column밖에 남지 않았다면 어쩔 수 없이 두 번째 경우를 선택해야함
    경우 1은 아예 선택할 수 없기 때문 -->state == 0*/ 

    for(i=0;i<7;i++){
      if(temp_arr[i]!=-100){state=1;break;}
    }

    if(state){
      while(1){
        i=rand()%7;
        if(temp_arr[i]!=-100){break;}
      }
    }
    else{
      while(1){
        i=rand()%7;
        if(check_row(copy, i)>=0){break;}
      }
    }
    printf("Rule 모드 판단 case 8\n");
    return i;
}
}



//column을 받아 그 자리에 돌을 두면 몇개의 threat을 <<생성>>하는지 useful인지 판단해서 리턴하는 함수
int make_threat(int arr[][7],int x,int turn){ //생성되는 threat의 수 useful이면 하나당 4 useless면 하나당 1
    int i,y;
    int temp_val=0;
    int copy_a[6][7];
    copyboard(arr,copy_a);

   for(i=5;i>=0;i--){
        if(copy_a[i][x]!=-1){
            y=i+1; break;
        }
        if(i==0){
            y=0;
        }
    }
    if(y==6){return -1;} //돌을 둘 수 있는 곳인지 판단
    copy_a[y][x]=turn%2; //내 돌을 놔봄

    temp_val=check_threat(copy_a,turn);

    if(temp_val>0){//threat을 생성하는지 체크
        copy_a[y][x]=-1; //시뮬레이션 했던 칸을 되돌려놓음
        return temp_val; //useful, useless threat의 갯수를 알려주는 함수 리턴값을 리턴
    }
    copy_a[y][x]=-1;
    return -1;
}

int check_threat(int arr[][7], int turn){
    int i,k;
    int count = 0;
    int copy_b[6][7];
    copyboard(arr,copy_b);

   for(i=0;i<6;i++){ //맨 아래 행부터 차례때로
        for(k=0;k<7;k++){ // 맨 왼쪽부터 차례대로
            if(copy_b[i][k]==-1){//빈칸에 대해
                copy_b[i][k]=turn%2;//내 돌을 둬봄
                if(check(copy_b)==1){//4돌 연결이 이루어지면 그자리는 threat인걸로 판단
                    if(useful(copy_b, i, k)==1){count+=4;}//threat이 useful인지 판단하고 그렇다면 +4
                    else{count+=1;}//useless라면 +1
                }
                copy_b[i][k]=-1;//시뮬레이션 해봤던 자리를 되돌려놓음
            }
        }
    }
    return count; //useful, useless threat의 갯수를 알려주는 count를 리턴함
}

int useful(int arr[][7], int tr, int tc){ //threat의 row column을 받아 useful인지 체크
//useful이면 1, useless면 0리턴
    if(tr==1){return 1;}
    if(arr[tr-1][tc]!=-1){return 1;}
    else return 0;
}

int check_bottom_1(int arr[][7], int x, int turn) //내 돌을 가정해서 둬 보고 그것이 상대방의 connect를 완성할 수 있게 해주는 것이라면 1리턴
{
    int i,y=0;
    int copy_c[6][7];
    copyboard(arr,copy_c);
    for(i=5;i>=0;i--){
        if(copy_c[i][x]!=-1){
            y=i+1; break;
        }
        if(i==0){
            y=0;
        }
    }
    copy_c[y][x]=turn%2; //내 돌을 놔봄

    if(y+1<=5){
      copy_c[y+1][x]=(turn+1)%2; //상대방으로 가정하여 돌을 둬봄
      if(check(copy_c)==1){ //상대방의 connect가 완성된다면
        copy_c[y+1][x]=-1;
        copy_c[y][x]=-1;
        return 1;
      }
    }
    else{
      copy_c[y][x]=-1;
      return 0; //해당 사항 없으면 0점
    }
}

int check_bottom_2(int arr[][7], int x, int turn) //내 돌을 가정해서 둬 보고 위에 언급했던 밑받침 상황이 발생하는지 체크
{ //리턴값이 -1이면 2번상황이면 2, 1번 상황이면 threat value에 따른 점수값
    int i,y=0;
    int copy_d[6][7];
    int temp_val=0;
    copyboard(arr,copy_d);
    for(i=5;i>=0;i--){
        if(copy_d[i][x]!=-1){
            y=i+1; break;
        }
        if(i==0){
            y=0;
        }
    }
    copy_d[y][x]=turn%2; //내 돌을 놔봄

    if(y+1<=5){
      copy_d[y+1][x]=(turn+1)%2; //그 위에 상대방으로 가정하여 돌을 둬봄
      temp_val=check_threat(copy_d,turn);

      if(temp_val>=1){ //상대방이 useless 혹은 useful threat을 생산해낸다면 
        copy_d[y+1][x]=-1;
        copy_d[y][x]=-1; //시뮬레이션 했던 칸을 되돌려놓음
        return temp_val; //useful, useless threat의 갯수를 알려주는 함수 리턴값을 리턴
      }
    }
    else{
      copy_d[y][x]=-1;
      return 0; //해당 사항 없으면 0점
    }
}

int check_row(int arr[][7], int x){ //둘 수 있는 column인지 체크하고 그렇다면 해당 row number리턴
    int i,y=0;
    for(i=5;i>=0;i--){
        if(arr[i][x]!=-1){
            y=i+1; break;
        }
        if(i==0){
            y=0;
        }
    }
    if(y==6){return -1;}//둘 수 없는 곳이라면 -1리턴
    return y;
}

